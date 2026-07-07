{-# OPTIONS --without-K --safe #-}

-- Compile-time spike test for Agdelte.Storage.Free: a toy verb signature with a LOCK DISCIPLINE.
-- Proves (all by `refl`, no runtime, no database):
--   * the freer Tx is total (module typechecks under --safe: no sized types, no TERMINATING);
--   * one reified program runs through a pure handler (the reference interpreter);
--   * read-your-own-writes holds across composition;
--   * the discipline checker REJECTS an unrooted write — a race becomes a deterministic red test.
module Agdelte.Storage.FreeTest where

open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Toy signature: a ℕ-keyed counter store with root locks
------------------------------------------------------------------------

data Req : Set where
  qLock : ℕ → Req            -- lockRoot (PG: SELECT … FOR UPDATE / pg_advisory_xact_lock)
  qGet  : ℕ → Req
  qPut  : ℕ → ℕ → Req

Ans : Req → Set
Ans (qLock _)  = ⊤
Ans (qGet _)   = Maybe ℕ
Ans (qPut _ _) = ⊤

data Err : Set where
  notLocked : Err            -- the discipline checker fired

open import Agdelte.Storage.Free Req Ans Err

------------------------------------------------------------------------
-- Native handler = reference semantics + lock-discipline checker
------------------------------------------------------------------------

St : Set
St = List (ℕ × ℕ) × List ℕ                      -- (assoc store, held root locks)

private
  member : ℕ → List ℕ → Bool
  member k []       = false
  member k (x ∷ xs) = if k ≡ᵇ x then true else member k xs

  lookupA : ℕ → List (ℕ × ℕ) → Maybe ℕ
  lookupA k []             = nothing
  lookupA k ((x , v) ∷ xs) = if k ≡ᵇ x then just v else lookupA k xs

  insertA : ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  insertA k v []             = (k , v) ∷ []
  insertA k v ((x , w) ∷ xs) = if k ≡ᵇ x then (k , v) ∷ xs else (x , w) ∷ insertA k v xs

handler : Handler St
handler (qLock r)  (kv , ls) = inj₂ (tt , (kv , r ∷ ls))
handler (qGet k)   (kv , ls) = inj₂ (lookupA k kv , (kv , ls))
handler (qPut k v) (kv , ls) =
  if member k ls then inj₂ (tt , (insertA k v kv , ls)) else inj₁ notLocked

------------------------------------------------------------------------
-- A disciplined command: lock the root, then check-then-write (race-free per root under RC)
------------------------------------------------------------------------

incr : ℕ → Tx ℕ
incr k =
  opT (qLock k) >>T
  opT (qGet k) >>=T λ old →
  opT (qPut k (suc (fromMaybe 0 old))) >>T
  returnT (suc (fromMaybe 0 old))

-- runs: fresh key → 1; lock recorded; write landed
_ : runTx handler (incr 7) ([] , []) ≡ inj₂ (1 , ((7 , 1) ∷ [] , 7 ∷ []))
_ = refl

-- read-your-own-writes across composition: the second incr sees the first one's write
_ : runTx handler (incr 7 >>T incr 7) ([] , []) ≡ inj₂ (2 , ((7 , 2) ∷ [] , 7 ∷ 7 ∷ []))
_ = refl

-- an UNROOTED write is rejected by the checker — the whole txn aborts (deterministically)
_ : runTx handler (opT (qPut 7 1)) ([] , []) ≡ inj₁ notLocked
_ = refl

-- abort short-circuits: nothing after the rejected verb runs
_ : runTx handler (opT (qPut 7 1) >>T incr 7) ([] , []) ≡ inj₁ notLocked
_ = refl
