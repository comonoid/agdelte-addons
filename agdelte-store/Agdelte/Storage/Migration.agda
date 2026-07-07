{-# OPTIONS --without-K #-}

-- Schema migrations as DATA (pg-store-plan): each step is a term with THREE interpreters —
-- `up` (SQL forward), `down` (SQL rollback; `nothing` = honestly irreversible), and `applyStep`
-- (the PURE MODEL: what the step does to the in-Agda schema set). The model is the point:
-- the chain is VERIFIED against the code — `migrate steps [] ≡ currentSchemas` by refl — so
-- changing a schema without writing its migration is a COMPILE ERROR. No external migration
-- tool can check that (it has no source of truth to compare with).
--
-- Runner: the existing ledger convention (schema_migrations, one txn per step — see
-- Agdelte.Server.Migrate) is reused with generated statements instead of *.sql files.
-- Column additions append at the END — the same Tier-1 evolution rule as the WAL codec.
module Agdelte.Storage.Migration where

open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.List using (List; []; _∷_; _++_; map; foldl; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.Storage.Schema using
  ( Schema; Column; col; ColTy; CMaybe; cname; cty; cindexed )
open import Agdelte.Storage.SQL using (ddlList; sqlTy; nullCon)

------------------------------------------------------------------------
-- The migration step language
------------------------------------------------------------------------

data MigStep : Set where
  mCreateTable : String → Schema → MigStep
  mAddColumn   : String → Column → String → MigStep   -- table, column, DEFAULT literal
                                                       -- ("" = none; REQUIRED for a NOT NULL column
                                                       --  on a table that may already hold rows)
  mAddIndex    : String → String → MigStep             -- table, column
  mDropIndex   : String → String → MigStep
  mDropColumn  : String → String → MigStep             -- irreversible (data gone)
  mDropTable   : String → MigStep                      -- irreversible
  mCreateSequence : String → MigStep                   -- surrogate-id source (invisible to the table model)

------------------------------------------------------------------------
-- Interpreter 1 — forward SQL (statement-per-element, audit A1)
------------------------------------------------------------------------

private
  idxStmt : String → String → String
  idxStmt t c = "CREATE INDEX IF NOT EXISTS \"" <> t <> "_" <> c <> "_idx\" ON \"" <> t <> "\" (\"" <> c <> "\");"

  dropIdxStmt : String → String → String
  dropIdxStmt t c = "DROP INDEX IF EXISTS \"" <> t <> "_" <> c <> "_idx\";"

  defSql : String → String
  defSql d = if primStringEquality d "" then "" else " DEFAULT " <> d

up : MigStep → List String
up (mCreateTable n s) = ddlList n s
up (mAddColumn t c d) =
  ("ALTER TABLE \"" <> t <> "\" ADD COLUMN \"" <> cname c <> "\" "
     <> sqlTy (cty c) <> nullCon (cty c) <> defSql d <> ";")
  ∷ (if cindexed c then idxStmt t (cname c) ∷ [] else [])
up (mAddIndex t c)   = idxStmt t c ∷ []
up (mDropIndex t c)  = dropIdxStmt t c ∷ []
up (mDropColumn t c) = ("ALTER TABLE \"" <> t <> "\" DROP COLUMN \"" <> c <> "\";") ∷ []
up (mDropTable t)    = ("DROP TABLE IF EXISTS \"" <> t <> "\";") ∷ []
up (mCreateSequence n) = ("CREATE SEQUENCE IF NOT EXISTS \"" <> n <> "\";") ∷ []

------------------------------------------------------------------------
-- Interpreter 2 — rollback SQL (`nothing` = irreversible, the runner refuses to roll past it)
------------------------------------------------------------------------

down : MigStep → Maybe (List String)
down (mCreateTable n _) = just (("DROP TABLE IF EXISTS \"" <> n <> "\";") ∷ [])
down (mAddColumn t c _) = just (("ALTER TABLE \"" <> t <> "\" DROP COLUMN \"" <> cname c <> "\";") ∷ [])
down (mAddIndex t c)    = just (dropIdxStmt t c ∷ [])
down (mDropIndex t c)   = just (idxStmt t c ∷ [])
down (mDropColumn _ _)  = nothing
down (mDropTable _)     = nothing
down (mCreateSequence n) = just (("DROP SEQUENCE IF EXISTS \"" <> n <> "\";") ∷ [])

------------------------------------------------------------------------
-- Interpreter 3 — the PURE MODEL over the schema set (the verification anchor)
------------------------------------------------------------------------

SchemaSet : Set
SchemaSet = List (String × Schema)

private
  adjust : String → (Schema → Schema) → SchemaSet → SchemaSet
  adjust t f [] = []
  adjust t f ((n , s) ∷ ss) =
    if primStringEquality n t then (n , f s) ∷ ss else (n , s) ∷ adjust t f ss

  setIdx : Bool → String → Schema → Schema
  setIdx b c [] = []
  setIdx b c (k ∷ ks) =
    if primStringEquality (cname k) c then col (cname k) (cty k) b ∷ ks else k ∷ setIdx b c ks

applyStep : MigStep → SchemaSet → SchemaSet
applyStep (mCreateTable n s) ss = ss ++ (n , s) ∷ []
applyStep (mAddColumn t c _) ss = adjust t (λ s → s ++ c ∷ []) ss      -- END-append (Tier-1)
applyStep (mAddIndex t c)    ss = adjust t (setIdx true c) ss
applyStep (mDropIndex t c)   ss = adjust t (setIdx false c) ss
applyStep (mDropColumn t c)  ss = adjust t (filterᵇ (λ k → not (primStringEquality (cname k) c))) ss
applyStep (mDropTable t)     ss = filterᵇ (λ p → not (primStringEquality (proj₁ p) t)) ss
applyStep (mCreateSequence _) ss = ss        -- sequences are not part of the table model

-- the whole chain, oldest first
migrate : List MigStep → SchemaSet → SchemaSet
migrate steps ss = foldl (λ acc st → applyStep st acc) ss steps