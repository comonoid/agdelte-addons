{-# OPTIONS --without-K #-}

-- Generic transaction monad over an embedded store, parameterized by the domain's
-- state `S`, operation `Op`, error `E`, and `apply : Op → S → S`. A `Txn A` threads
-- the working state and an accumulator of emitted ops; it either aborts with `E`
-- (nothing committed) or yields a new state, the ops it emitted, and a result.
--
-- The single mutating primitive `emit op` BOTH applies the op to the working state
-- (so later reads see it) AND records it for the WAL. Because it uses the very same
-- `apply` the WAL replays, the live result equals the replayed result by
-- construction (live ≡ replay). The op accumulator is a DIFFERENCE LIST (O(1) snoc)
-- so a bulk/cascade transaction is O(n), not O(n²).
--
-- `runTxn` produces exactly the `S → E ⊎ (S × List Op × A)` shape that
-- `Agdelte.Storage.WAL.walTxn` consumes.
--
-- A domain instantiates this: `open import Agdelte.Storage.Txn S Op E apply`.
module Agdelte.Storage.Txn (S Op E : Set) (apply : Op → S → S) where

open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Difference list of ops (O(1) snoc)
------------------------------------------------------------------------

private
  DList : Set
  DList = List Op → List Op

  dnil : DList
  dnil xs = xs

  dsnoc : DList → Op → DList
  dsnoc d op xs = d (op ∷ xs)

  drun : DList → List Op
  drun d = d []

------------------------------------------------------------------------
-- The monad
------------------------------------------------------------------------

-- working state → ops-so-far → abort | (new state × ops × result)
Txn : Set → Set
Txn A = S → DList → E ⊎ (S × DList × A)

returnT : ∀ {A} → A → Txn A
returnT a s d = inj₂ (s , d , a)

infixl 1 _>>=T_ _>>T_

_>>=T_ : ∀ {A B} → Txn A → (A → Txn B) → Txn B
(m >>=T f) s d with m s d
... | inj₁ e             = inj₁ e
... | inj₂ (s' , d' , a) = f a s' d'

_>>T_ : ∀ {A B} → Txn A → Txn B → Txn B
m >>T n = m >>=T λ _ → n

------------------------------------------------------------------------
-- Primitives
------------------------------------------------------------------------

-- read the current working state (reflects ops emitted earlier in this txn)
getBase : Txn S
getBase s d = inj₂ (s , d , s)

-- reject the whole transaction; nothing is committed
abort : ∀ {A} → E → Txn A
abort e s d = inj₁ e

-- apply op to the working state AND record it for the WAL (the only mutation)
emit : Op → Txn ⊤
emit op s d = inj₂ (apply op s , dsnoc d op , tt)

------------------------------------------------------------------------
-- Derived combinators (so domain commands read like ordinary FP)
------------------------------------------------------------------------

-- continue with `a`, or abort with `e`
require : ∀ {A : Set} → (A ⊎ E) → Txn A
require (inj₁ a) s d = inj₂ (s , d , a)
require (inj₂ e) s d = inj₁ e

-- unwrap a lookup or abort with the given error (FK / existence checks)
requireJust : ∀ {A} → E → Maybe A → Txn A
requireJust e nothing  = abort e
requireJust e (just a) = returnT a

-- continue iff the guard holds, else abort (invariants / slot-free / transitions)
guardT : Bool → E → Txn ⊤
guardT true  _ = returnT tt
guardT false e = abort e

-- emit once per element, in order (cascades over reverse-index id lists)
forEachT : ∀ {A : Set} → List A → (A → Txn ⊤) → Txn ⊤
forEachT []       f = returnT tt
forEachT (x ∷ xs) f = f x >>T forEachT xs f

------------------------------------------------------------------------
-- Run — to the shape walTxn consumes
------------------------------------------------------------------------

runTxn : ∀ {A} → Txn A → S → E ⊎ (S × (List Op × A))
runTxn m s with m s dnil
... | inj₁ e            = inj₁ e
... | inj₂ (s' , d , a) = inj₂ (s' , drun d , a)
