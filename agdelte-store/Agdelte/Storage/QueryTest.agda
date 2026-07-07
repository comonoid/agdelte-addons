{-# OPTIONS --without-K #-}

-- Compile-time test of the query-EDSL: BOTH interpreters of one reified metaKPI-style query are
-- pinned by `refl` — the native fold counts exactly the matching rows, and the compiler emits
-- exactly the asserted conformant SELECT. (The live half of the diff-test — run the compiled SQL
-- on real PG over the same rows and compare with the native count — waits for the txn driver.)
module Agdelte.Storage.QueryTest where

open import Agda.Builtin.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Storage.Schema using (Schema; mkCol; idxCol; CNat; CStr; CFK; Row)
open import Agdelte.Storage.Query using (Count; countWhere; eqN; runCount; compileCount)

-- a knowledge-shaped toy schema (id, subject FK, tenant FK, opaque detail)
kSchema : Schema
kSchema = mkCol "id" CNat ∷ idxCol "subject" (CFK "subject")
        ∷ mkCol "tenant" (CFK "tenant") ∷ mkCol "detail" CStr ∷ []

-- the metaKPI-style query: knowledge rows of subject 5 within tenant 2
metaKpi : Count kSchema
metaKpi = countWhere "knowledge" (eqN "subject" 5 ∷ eqN "tenant" 2 ∷ [])

r1 r2 r3 r4 : Row kSchema
r1 = 1 , 5 , 2 , "match" , tt
r2 = 2 , 5 , 3 , "wrong tenant" , tt
r3 = 3 , 6 , 2 , "wrong subject" , tt
r4 = 4 , 5 , 2 , "match too" , tt

-- native fold: exactly the two matching rows
_ : runCount metaKpi (r1 ∷ r2 ∷ r3 ∷ r4 ∷ []) ≡ 2
_ = refl

-- compiler: exactly this SQL, nothing implicit (no trailing ";" — G1: runs inside a queryConn
-- subquery wrapper; COUNT(*) aliased so the JSON result carries a "count" field)
_ : compileCount metaKpi ≡
    "SELECT COUNT(*) AS \"count\" FROM \"knowledge\" WHERE \"subject\" = 5 AND \"tenant\" = 2"
_ = refl

-- degenerate query (no predicates) stays deterministic: WHERE TRUE
_ : compileCount (countWhere {s = kSchema} "knowledge" []) ≡
    "SELECT COUNT(*) AS \"count\" FROM \"knowledge\" WHERE TRUE"
_ = refl
