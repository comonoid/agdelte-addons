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
  -- Schema-HARDENING indexes (perf + natural-key). MODEL-INVISIBLE by design: they emit a PG
  -- index but do NOT mark the column `cindexed`, so they never enter the byIx position scheme
  -- (idxCols) — that is the compile-time secondary-index layer, this is a deployment concern.
  mIndexU : String → String → MigStep                  -- CREATE UNIQUE INDEX (table, column)
  mIndexP : String → String → MigStep                  -- CREATE INDEX        (table, column)

------------------------------------------------------------------------
-- Interpreter 1 — forward SQL (statement-per-element, audit A1)
------------------------------------------------------------------------

private
  idxStmt : String → String → String
  idxStmt t c = "CREATE INDEX IF NOT EXISTS \"" <> t <> "_" <> c <> "_idx\" ON \"" <> t <> "\" (\"" <> c <> "\");"

  dropIdxStmt : String → String → String
  dropIdxStmt t c = "DROP INDEX IF EXISTS \"" <> t <> "_" <> c <> "_idx\";"

  uidxStmt : String → String → String
  uidxStmt t c = "CREATE UNIQUE INDEX IF NOT EXISTS \"" <> t <> "_" <> c <> "_uidx\" ON \"" <> t <> "\" (\"" <> c <> "\");"

  dropUidxStmt : String → String → String
  dropUidxStmt t c = "DROP INDEX IF EXISTS \"" <> t <> "_" <> c <> "_uidx\";"

  -- perf-index name uses a DISTINCT `_pidx` suffix (not `_idx`) so a hardening index can never
  -- collide with a byIx secondary index on the same column (which idxStmt names `_idx`).
  pidxStmt : String → String → String
  pidxStmt t c = "CREATE INDEX IF NOT EXISTS \"" <> t <> "_" <> c <> "_pidx\" ON \"" <> t <> "\" (\"" <> c <> "\");"

  dropPidxStmt : String → String → String
  dropPidxStmt t c = "DROP INDEX IF EXISTS \"" <> t <> "_" <> c <> "_pidx\";"

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
up (mIndexU t c) = uidxStmt t c ∷ []
up (mIndexP t c) = pidxStmt t c ∷ []

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
down (mIndexU t c) = just (dropUidxStmt t c ∷ [])
down (mIndexP t c) = just (dropPidxStmt t c ∷ [])

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
applyStep (mIndexU _ _) ss = ss              -- hardening indexes are model-invisible (see MigStep)
applyStep (mIndexP _ _) ss = ss

-- the whole chain, oldest first
migrate : List MigStep → SchemaSet → SchemaSet
migrate steps ss = foldl (λ acc st → applyStep st acc) ss steps

------------------------------------------------------------------------
-- Interpreter 4 — wellformedness of a migration chain (PURE; refl-gated in the registry).
-- Each step is checked against the model AS EVOLVED by all prior steps, so structural mistakes
-- (create an existing table, add a duplicate/absent column, index/drop a missing column, drop a
-- missing table, a nullable-of-nullable column) are caught at TYPECHECK, before any SQL runs.
------------------------------------------------------------------------

data WfError : Set where
  wfDupTable       : String → WfError            -- CREATE TABLE whose name already exists
  wfNoTable        : String → WfError            -- op targets a table not in the model
  wfDupColumn      : String → String → WfError   -- ADD COLUMN that already exists (table, col)
  wfNoColumn       : String → String → WfError   -- INDEX/DROP a column that isn't there
  wfDupColInCreate : String → String → WfError   -- duplicate column name inside one CREATE TABLE
  wfNestedMaybe    : String → String → WfError   -- CMaybe (CMaybe _) — nullable of nullable

private
  hasTable : String → SchemaSet → Bool
  hasTable t [] = false
  hasTable t ((n , _) ∷ ss) = if primStringEquality n t then true else hasTable t ss

  colsOf : String → SchemaSet → Schema
  colsOf t [] = []
  colsOf t ((n , s) ∷ ss) = if primStringEquality n t then s else colsOf t ss

  hasCol : String → Schema → Bool
  hasCol c [] = false
  hasCol c (k ∷ ks) = if primStringEquality (cname k) c then true else hasCol c ks

  nested? : ColTy → Bool
  nested? (CMaybe (CMaybe _)) = true
  nested? _                   = false

  dupNames : Schema → List String                 -- names that recur (reported on the 2nd hit)
  dupNames []       = []
  dupNames (k ∷ ks) = (if hasCol (cname k) ks then cname k ∷ [] else []) ++ dupNames ks

  nestedCols : Schema → List String
  nestedCols []       = []
  nestedCols (k ∷ ks) = (if nested? (cty k) then cname k ∷ [] else []) ++ nestedCols ks

checkStep : MigStep → SchemaSet → List WfError
checkStep (mCreateTable n s) ss =
  (if hasTable n ss then wfDupTable n ∷ [] else [])
    ++ map (wfDupColInCreate n) (dupNames s)
    ++ map (wfNestedMaybe n) (nestedCols s)
checkStep (mAddColumn t c _) ss =
  if not (hasTable t ss) then wfNoTable t ∷ []
  else (if hasCol (cname c) (colsOf t ss) then wfDupColumn t (cname c) ∷ [] else [])
         ++ (if nested? (cty c) then wfNestedMaybe t (cname c) ∷ [] else [])
checkStep (mAddIndex t c) ss =
  if not (hasTable t ss) then wfNoTable t ∷ []
  else (if hasCol c (colsOf t ss) then [] else wfNoColumn t c ∷ [])
checkStep (mDropIndex t c) ss =
  if not (hasTable t ss) then wfNoTable t ∷ []
  else (if hasCol c (colsOf t ss) then [] else wfNoColumn t c ∷ [])
checkStep (mDropColumn t c) ss =
  if not (hasTable t ss) then wfNoTable t ∷ []
  else (if hasCol c (colsOf t ss) then [] else wfNoColumn t c ∷ [])
checkStep (mDropTable t) ss =
  if hasTable t ss then [] else wfNoTable t ∷ []
checkStep (mCreateSequence _) _ = []
-- a hardening index must target an existing table + column (catches a typo in the index list)
checkStep (mIndexU t c) ss =
  if not (hasTable t ss) then wfNoTable t ∷ []
  else (if hasCol c (colsOf t ss) then [] else wfNoColumn t c ∷ [])
checkStep (mIndexP t c) ss =
  if not (hasTable t ss) then wfNoTable t ∷ []
  else (if hasCol c (colsOf t ss) then [] else wfNoColumn t c ∷ [])

-- all errors across the chain (empty ⇒ wellformed); the model evolves step by step.
checkMigrations : List MigStep → SchemaSet → List WfError
checkMigrations []         _  = []
checkMigrations (st ∷ sts) ss = checkStep st ss ++ checkMigrations sts (applyStep st ss)

wellFormed : List MigStep → SchemaSet → Bool
wellFormed steps ss with checkMigrations steps ss
... | [] = true
... | _  = false