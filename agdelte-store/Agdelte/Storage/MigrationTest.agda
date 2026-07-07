{-# OPTIONS --without-K #-}

-- Compile-time proofs for the migration EDSL. The headline property: the migration CHAIN,
-- replayed through the pure model from an empty database, yields EXACTLY the current schema —
-- by refl. Change the schema without its migration (or vice versa) ⇒ this module stops compiling.
module Agdelte.Storage.MigrationTest where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Storage.Schema using (Schema; mkCol; idxCol; CNat; CStr; CBool; CMaybe; CFK)
open import Agdelte.Storage.Migration using
  ( MigStep; mCreateTable; mCreateSequence; mAddColumn; mAddIndex; mDropIndex; mDropColumn; mDropTable
  ; mIndexU; mIndexP
  ; up; down; migrate; SchemaSet
  ; checkStep; checkMigrations
  ; wfDupTable; wfNoTable; wfDupColumn; wfNoColumn; wfDupColInCreate; wfNestedMaybe )

-- v1 of a table, as it once shipped
acctV1 : Schema
acctV1 = mkCol "id" CNat ∷ mkCol "tenant" (CFK "tenant") ∷ mkCol "email" CStr ∷ []

-- the CURRENT schema in code (as it would live in Wire.agda today):
-- tenant got an index, verified and revoked_at were appended (Tier-1: at the END)
acctNow : Schema
acctNow = mkCol "id" CNat ∷ idxCol "tenant" (CFK "tenant") ∷ mkCol "email" CStr
        ∷ mkCol "verified" CBool ∷ mkCol "revoked_at" (CMaybe CNat) ∷ []

-- the migration history, oldest first
history : List MigStep
history =
    mCreateTable "acct" acctV1
  ∷ mAddColumn "acct" (mkCol "verified" CBool) "FALSE"     -- NOT NULL ⇒ DEFAULT required
  ∷ mAddColumn "acct" (mkCol "revoked_at" (CMaybe CNat)) ""
  ∷ mAddIndex "acct" "tenant"
  ∷ []

-- ★ THE check: replaying history through the model ≡ the current code schema. refl or bust.
_ : migrate history [] ≡ ("acct" , acctNow) ∷ []
_ = refl

-- forward SQL is exactly what we assert (golden, per statement — audit A1 form)
_ : up (mAddColumn "acct" (mkCol "verified" CBool) "FALSE")
  ≡ ("ALTER TABLE \"acct\" ADD COLUMN \"verified\" BOOLEAN NOT NULL DEFAULT FALSE;") ∷ []
_ = refl

_ : up (mAddColumn "acct" (mkCol "revoked_at" (CMaybe CNat)) "")
  ≡ ("ALTER TABLE \"acct\" ADD COLUMN \"revoked_at\" BIGINT;") ∷ []
_ = refl

_ : up (mAddIndex "acct" "tenant")
  ≡ ("CREATE INDEX IF NOT EXISTS \"acct_tenant_idx\" ON \"acct\" (\"tenant\");") ∷ []
_ = refl

-- rollback SQL: additive steps invert…
_ : down (mAddColumn "acct" (mkCol "verified" CBool) "FALSE")
  ≡ just (("ALTER TABLE \"acct\" DROP COLUMN \"verified\";") ∷ [])
_ = refl

_ : down (mAddIndex "acct" "tenant")
  ≡ just (("DROP INDEX IF EXISTS \"acct_tenant_idx\";") ∷ [])
_ = refl

-- …а деструктивные — честно необратимы (раннер не откатит дальше этой точки)
_ : down (mDropColumn "acct" "email") ≡ nothing
_ = refl

-- model-level invertibility of an additive pair: add-then-drop restores v1 exactly
_ : migrate ( mAddColumn "acct" (mkCol "verified" CBool) "FALSE"
            ∷ mDropColumn "acct" "verified" ∷ [] ) (("acct" , acctV1) ∷ [])
  ≡ ("acct" , acctV1) ∷ []
_ = refl

-- audit D1: the sequence step (fresh deploys need the surrogate-id source before any INSERT)
_ : up (mCreateSequence "cxm_id_seq") ≡ ("CREATE SEQUENCE IF NOT EXISTS \"cxm_id_seq\";") ∷ []
_ = refl
_ : down (mCreateSequence "cxm_id_seq") ≡ just (("DROP SEQUENCE IF EXISTS \"cxm_id_seq\";") ∷ [])
_ = refl

------------------------------------------------------------------------
-- Wellformedness (interpreter 4). POSITIVE: the good chain is clean. NEGATIVES: the checker has
-- TEETH — each structural mistake is reported (a `λ _ _ → []` stub would fail every case below).
------------------------------------------------------------------------

_ : checkMigrations history [] ≡ []
_ = refl

-- create a table that already exists
_ : checkStep (mCreateTable "acct" acctV1) (("acct" , acctV1) ∷ []) ≡ wfDupTable "acct" ∷ []
_ = refl

-- add a column to a table that isn't there
_ : checkStep (mAddColumn "ghost" (mkCol "x" CNat) "") [] ≡ wfNoTable "ghost" ∷ []
_ = refl

-- add a column that already exists
_ : checkStep (mAddColumn "acct" (mkCol "email" CStr) "") (("acct" , acctV1) ∷ [])
  ≡ wfDupColumn "acct" "email" ∷ []
_ = refl

-- drop / index a column that isn't there
_ : checkStep (mDropColumn "acct" "ghost") (("acct" , acctV1) ∷ []) ≡ wfNoColumn "acct" "ghost" ∷ []
_ = refl

-- duplicate column name inside one CREATE TABLE
_ : checkStep (mCreateTable "dup" (mkCol "id" CNat ∷ mkCol "x" CNat ∷ mkCol "x" CStr ∷ []))  []
  ≡ wfDupColInCreate "dup" "x" ∷ []
_ = refl

-- a nullable-of-nullable column
_ : checkStep (mCreateTable "bad" (mkCol "id" CNat ∷ mkCol "x" (CMaybe (CMaybe CNat)) ∷ [])) []
  ≡ wfNestedMaybe "bad" "x" ∷ []
_ = refl

------------------------------------------------------------------------
-- Hardening indexes (mIndexU/mIndexP) — perf + natural-key, MODEL-INVISIBLE (schema audit).
------------------------------------------------------------------------

-- forward SQL: UNIQUE vs plain, distinct index names (_uidx / _idx)
_ : up (mIndexU "user" "login")
  ≡ ("CREATE UNIQUE INDEX IF NOT EXISTS \"user_login_uidx\" ON \"user\" (\"login\");") ∷ []
_ = refl
_ : up (mIndexP "identity" "external_id")
  ≡ ("CREATE INDEX IF NOT EXISTS \"identity_external_id_pidx\" ON \"identity\" (\"external_id\");") ∷ []
_ = refl

-- both roll back (DROP INDEX on the matching name)
_ : down (mIndexU "user" "login") ≡ just (("DROP INDEX IF EXISTS \"user_login_uidx\";") ∷ [])
_ = refl
_ : down (mIndexP "identity" "external_id") ≡ just (("DROP INDEX IF EXISTS \"identity_external_id_pidx\";") ∷ [])
_ = refl

-- MODEL-INVISIBLE: neither touches the schema set (so byIx positions / migrate-watch are untouched)
_ : migrate (mIndexU "acct" "email" ∷ mIndexP "acct" "email" ∷ []) (("acct" , acctV1) ∷ [])
  ≡ ("acct" , acctV1) ∷ []
_ = refl

-- but still validated: a hardening index on a missing table/column is caught
_ : checkStep (mIndexP "ghost" "x") [] ≡ wfNoTable "ghost" ∷ []
_ = refl
_ : checkStep (mIndexU "acct" "ghost") (("acct" , acctV1) ∷ []) ≡ wfNoColumn "acct" "ghost" ∷ []
_ = refl
