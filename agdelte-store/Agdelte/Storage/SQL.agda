{-# OPTIONS --without-K #-}

-- Interpreter 2 of a Schema (cf. Schema.agda's "Interpreter 1 — the WAL codec"): SQL DDL for a
-- Postgres backend, derived from the SAME schema that drives the WAL codec — so WAL and PG stay
-- structurally identical ("Postgres = another interpreter of the same schema", recomposition Р3).
--
-- Pure String → String generators: no FFI, no live PG needed to unit-test (assert the emitted SQL).
-- Row → INSERT (dependent traversal of `Row schema`) lands in a follow-up; this module is the DDL half.
module Agdelte.Storage.SQL where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String using (String; toList; fromList) renaming (_++_ to _<>_)
open import Agda.Builtin.Char using (primCharEquality)

open import Agdelte.Storage.Schema using
  ( Schema; Column; ColTy; CNat; CStr; CBool; CEnum; CEnumS; CMaybe; CFK
  ; cname; cty; cindexed; ⟦_⟧; Row )

------------------------------------------------------------------------
-- ColTy → SQL
------------------------------------------------------------------------

-- Physical SQL type. Enums store their ordinal (SMALLINT), matching Schema's `⟦ CEnum ⟧ = ℕ`.
-- CMaybe unwraps to the inner type; nullability is emitted separately by `nullCon`.
sqlTy : ColTy → String
sqlTy CNat       = "BIGINT"
sqlTy CStr       = "TEXT"
sqlTy CBool      = "BOOLEAN"
sqlTy (CEnum _)  = "SMALLINT"
sqlTy (CEnumS _) = "SMALLINT"
sqlTy (CFK _)    = "BIGINT"
sqlTy (CMaybe t) = sqlTy t

-- CMaybe ⇒ nullable; every other column is NOT NULL (Schema has no free-floating nulls).
nullCon : ColTy → String
nullCon (CMaybe _) = ""
nullCon _          = " NOT NULL"

------------------------------------------------------------------------
-- CREATE TABLE (first column = surrogate PK, by Schema convention)
------------------------------------------------------------------------

private
  colSql : Column → String
  colSql c = "\"" <> cname c <> "\" " <> sqlTy (cty c) <> nullCon (cty c)

  -- non-PK columns, each prefixed with ", "
  restCols : Schema → String
  restCols []       = ""
  restCols (c ∷ cs) = ", " <> colSql c <> restCols cs

  bodyCols : Schema → String
  bodyCols []       = ""                                   -- empty schema ⇒ no columns
  bodyCols (c ∷ cs) = colSql c <> " PRIMARY KEY" <> restCols cs

createTable : String → Schema → String
createTable name s = "CREATE TABLE IF NOT EXISTS \"" <> name <> "\" (" <> bodyCols s <> ");"

------------------------------------------------------------------------
-- Secondary indexes — one CREATE INDEX per `cindexed` column
------------------------------------------------------------------------

private
  indexStatements : String → Schema → List String
  indexStatements _    []       = []
  indexStatements name (c ∷ cs) =
    if cindexed c
    then ("CREATE INDEX IF NOT EXISTS \"" <> name <> "_" <> cname c <> "_idx\" ON \""
            <> name <> "\" (\"" <> cname c <> "\");") ∷ indexStatements name cs
    else indexStatements name cs

-- Full DDL for one table as SEPARATE statements (audit A1: drivers on the extended protocol
-- reject multi-statement strings — run each element with its own execConn/execSql call).
ddlList : String → Schema → List String
ddlList name s = createTable name s ∷ indexStatements name s

-- the same DDL as one display string (simple-protocol / logs); defined VIA ddlList so the
-- refl-tests pin both forms at once.
schemaDDL : String → Schema → String
schemaDDL name s = joinSp (ddlList name s)
  where joinSp : List String → String
        joinSp []           = ""
        joinSp (x ∷ [])     = x
        joinSp (x ∷ y ∷ xs) = x <> " " <> joinSp (y ∷ xs)

------------------------------------------------------------------------
-- Row → INSERT — a typed row (same `Row schema` the WAL codec encodes) → one INSERT statement
------------------------------------------------------------------------

private
  -- SQL string literal: single-quote wrapped, embedded quotes doubled (standard_conforming_strings
  -- ⇒ backslashes are literal, so only ' needs escaping). Guards apostrophes in notes/names.
  esc : List Char → String
  esc []       = ""
  esc (c ∷ cs) = (if primCharEquality c '\'' then "''" else fromList (c ∷ [])) <> esc cs

  sqlStr : String → String
  sqlStr s = "'" <> esc (toList s) <> "'"

-- one column value → SQL literal, by its declared type. CMaybe nothing → NULL.
litOf : (t : ColTy) → ⟦ t ⟧ → String
litOf CNat       n        = show n
litOf CStr       s        = sqlStr s
litOf CBool      true     = "TRUE"
litOf CBool      false    = "FALSE"
litOf (CEnum _)  n        = show n
litOf (CEnumS _) n        = show n
litOf (CFK _)    n        = show n
litOf (CMaybe t) (just v) = litOf t v
litOf (CMaybe t) nothing  = "NULL"

private
  colNames : Schema → String
  colNames []             = ""
  colNames (c ∷ [])       = "\"" <> cname c <> "\""
  colNames (c ∷ c′ ∷ cs)  = "\"" <> cname c <> "\", " <> colNames (c′ ∷ cs)

  rowLits : (s : Schema) → Row s → String
  rowLits []             _       = ""
  rowLits (c ∷ [])       (v , _) = litOf (cty c) v
  rowLits (c ∷ c′ ∷ cs)  (v , r) = litOf (cty c) v <> ", " <> rowLits (c′ ∷ cs) r

rowInsert : String → (s : Schema) → Row s → String
rowInsert name s r =
  "INSERT INTO \"" <> name <> "\" (" <> colNames s <> ") VALUES (" <> rowLits s r <> ");"

------------------------------------------------------------------------
-- put / del / select — the live-backend verbs (store `SetX` = UPSERT by pk, `DelX` = DELETE by pk)
------------------------------------------------------------------------

private
  pkName : Schema → String                                   -- surrogate PK = first column, by convention
  pkName []      = "id"
  pkName (c ∷ _) = cname c

  -- "c=EXCLUDED.c, …" over the given (non-pk) columns
  setExcl : Schema → String
  setExcl []            = ""
  setExcl (c ∷ [])      = "\"" <> cname c <> "\"=EXCLUDED.\"" <> cname c <> "\""
  setExcl (c ∷ c′ ∷ cs) = "\"" <> cname c <> "\"=EXCLUDED.\"" <> cname c <> "\", " <> setExcl (c′ ∷ cs)

  onConflict : Schema → String
  onConflict []             = ""
  onConflict (c ∷ [])       = " ON CONFLICT (\"" <> cname c <> "\") DO NOTHING"          -- pk-only table
  onConflict (c ∷ c′ ∷ cs)  = " ON CONFLICT (\"" <> cname c <> "\") DO UPDATE SET " <> setExcl (c′ ∷ cs)

-- `putT` semantics: insert-or-replace by pk.
rowUpsert : String → (s : Schema) → Row s → String
rowUpsert name s r =
  "INSERT INTO \"" <> name <> "\" (" <> colNames s <> ") VALUES (" <> rowLits s r <> ")"
    <> onConflict s <> ";"

-- `delT` semantics: delete by pk.
deleteById : String → Schema → ℕ → String
deleteById name s pk =
  "DELETE FROM \"" <> name <> "\" WHERE \"" <> pkName s <> "\" = " <> show pk <> ";"

------------------------------------------------------------------------
-- SELECT — reads become bounded queries into a temporary result set (SELECT * ⇒ schema-ordered rows)
------------------------------------------------------------------------

-- Every result set is pinned `ORDER BY pk` — «мы — стандарт» (pg-store-plan): the native
-- interpreters read id-ordered state, so the compiled SQL must never rely on PG's arbitrary
-- physical order (a first-match over an unordered result would be nondeterministic).
selectAll : String → Schema → String
selectAll name s = "SELECT * FROM \"" <> name <> "\" ORDER BY \"" <> pkName s <> "\""

selectByNat : String → Schema → (col : String) → ℕ → String   -- byIndex / by pk / by ℕ-column
selectByNat name s col key =
  "SELECT * FROM \"" <> name <> "\" WHERE \"" <> col <> "\" = " <> show key
    <> " ORDER BY \"" <> pkName s <> "\""

selectByStr : String → Schema → (col : String) → String → String   -- byCol (login/name/token/…)
selectByStr name s col key =
  "SELECT * FROM \"" <> name <> "\" WHERE \"" <> col <> "\" = " <> sqlStr key
    <> " ORDER BY \"" <> pkName s <> "\""

selectPage : String → Schema → (off lim : ℕ) → String      -- bucket D: stable pagination by pk
selectPage name s off lim =
  "SELECT * FROM \"" <> name <> "\" ORDER BY \"" <> pkName s <> "\" LIMIT " <> show lim <> " OFFSET " <> show off
