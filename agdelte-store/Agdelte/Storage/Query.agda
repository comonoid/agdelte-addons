{-# OPTIONS --without-K #-}

-- Minimal query-EDSL (PG-store plan, спайк ч.3): single-table filter + COUNT, with TWO
-- interpreters over one reified query — the native fold (reference semantics, runs without PG)
-- and a compiler to one conformant SELECT. Typing is deliberately modest (fork-4 decision):
-- columns are referenced by name, guarded by a compile-time `T (hasNatCol …)` check (the idxCol
-- trick) — convenient on the Agda side, no dependent plumbing. Verbs grow on demand (sum/group/
-- order come when a hot path needs them), never handwritten PL/pgSQL.
module Agdelte.Storage.Query where

open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; T)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.Storage.Schema using
  ( Schema; Column; ColTy; CNat; CStr; CBool; CEnum; CEnumS; CMaybe; CFK
  ; cname; cty; ⟦_⟧; Row )

------------------------------------------------------------------------
-- Named-column access, guarded at construction time
------------------------------------------------------------------------

-- ℕ-valued column kinds (same set as Schema.isIndexable minus CBool: comparisons are on ℕ)
natValued : ColTy → Bool
natValued CNat       = true
natValued (CFK _)    = true
natValued (CEnum _)  = true
natValued (CEnumS _) = true
natValued _          = false

hasNatCol : Schema → String → Bool
hasNatCol []       _ = false
hasNatCol (c ∷ cs) n = (primStringEquality (cname c) n ∧ natValued (cty c)) ∨ hasNatCol cs n

-- read the ℕ value of a named column off a typed row (nothing on non-nat/missing — unreachable
-- for predicates built through the T-guard, but total regardless)
natAt : (s : Schema) → String → Row s → Maybe ℕ
natAt []       _ _       = nothing
natAt (c ∷ cs) n (v , r) =
  if primStringEquality (cname c) n then natVal (cty c) v else natAt cs n r
  where
    natVal : (t : ColTy) → ⟦ t ⟧ → Maybe ℕ
    natVal CNat       x = just x
    natVal (CFK _)    x = just x
    natVal (CEnum _)  x = just x
    natVal (CEnumS _) x = just x
    natVal CStr       _ = nothing
    natVal CBool      _ = nothing
    natVal (CMaybe _) _ = nothing

------------------------------------------------------------------------
-- The reified query: conjunctive ℕ-equality filter + COUNT
------------------------------------------------------------------------

data Pred (s : Schema) : Set where
  eqN : (col : String) → {T (hasNatCol s col)} → ℕ → Pred s   -- "col" = n (col must exist, ℕ-valued)

record Count (s : Schema) : Set where
  constructor countWhere
  field table : String
        preds : List (Pred s)
open Count public

------------------------------------------------------------------------
-- Interpreter 1 — the native fold (reference semantics; the test/diff baseline)
------------------------------------------------------------------------

evalPred : ∀ {s} → Pred s → Row s → Bool
evalPred {s} (eqN col n) r with natAt s col r
... | just m  = m ≡ᵇ n
... | nothing = false

matches : ∀ {s} → List (Pred s) → Row s → Bool
matches []       _ = true
matches (p ∷ ps) r = evalPred p r ∧ matches ps r

runCount : ∀ {s} → Count s → List (Row s) → ℕ
runCount q = foldr (λ r acc → if matches (preds q) r then suc acc else acc) 0

------------------------------------------------------------------------
-- Interpreter 2 — the SQL compiler (one conformant SELECT; COUNT needs no ORDER pinning)
------------------------------------------------------------------------

private
  predSql : ∀ {s} → Pred s → String
  predSql (eqN col n) = "\"" <> col <> "\" = " <> show n

  conj : ∀ {s} → List (Pred s) → String
  conj []           = "TRUE"
  conj (p ∷ [])     = predSql p
  conj (p ∷ q ∷ ps) = predSql p <> " AND " <> conj (q ∷ ps)

-- NB: NO trailing ";" — this SELECT is executed through the read path (queryConn), which wraps it
-- as `… FROM (<sql>) _q`, and a ";" inside a subquery is a syntax error (the same G1 rule the
-- Storage.SQL SELECT generators follow). Direct-exec paths tolerate its absence.
compileCount : ∀ {s} → Count s → String
compileCount q = "SELECT COUNT(*) AS \"count\" FROM \"" <> table q <> "\" WHERE " <> conj (preds q)
