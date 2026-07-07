{-# OPTIONS --without-K #-}

-- Compile-time test of the Schema→DDL interpreter: a `refl` proof pins the emitted SQL exactly.
-- If this module typechecks, `schemaDDL` produces precisely the asserted string (no live PG needed).
module Agdelte.Storage.SQLTest where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Bool using (true; false)
open import Data.Product using (_,_)
open import Agda.Builtin.Unit using (tt)

open import Agdelte.Storage.Schema using
  ( Schema; mkCol; idxCol; CNat; CStr; CBool; CMaybe; CFK )
open import Agdelte.Storage.SQL using (schemaDDL; ddlList; rowInsert; rowUpsert; deleteById; selectByNat; selectByStr)

-- a representative schema: PK + indexed FK + text + bool + nullable-nat (like an identity/token row)
acctSchema : Schema
acctSchema = mkCol "id" CNat
           ∷ idxCol "tenant" (CFK "tenant")
           ∷ mkCol "email" CStr
           ∷ mkCol "verified" CBool
           ∷ mkCol "revoked_at" (CMaybe CNat)
           ∷ []

_ : schemaDDL "acct" acctSchema ≡
    "CREATE TABLE IF NOT EXISTS \"acct\" (\"id\" BIGINT NOT NULL PRIMARY KEY, \"tenant\" BIGINT NOT NULL, \"email\" TEXT NOT NULL, \"verified\" BOOLEAN NOT NULL, \"revoked_at\" BIGINT); CREATE INDEX IF NOT EXISTS \"acct_tenant_idx\" ON \"acct\" (\"tenant\");"
_ = refl

-- audit A1: DDL as separate statements (extended-protocol drivers reject multi-statement strings)
_ : ddlList "acct" acctSchema ≡
    ( "CREATE TABLE IF NOT EXISTS \"acct\" (\"id\" BIGINT NOT NULL PRIMARY KEY, \"tenant\" BIGINT NOT NULL, \"email\" TEXT NOT NULL, \"verified\" BOOLEAN NOT NULL, \"revoked_at\" BIGINT);"
    ∷ "CREATE INDEX IF NOT EXISTS \"acct_tenant_idx\" ON \"acct\" (\"tenant\");" ∷ [] )
_ = refl

-- INSERT: FK/nat → decimal, TEXT → quoted+escaped ('' for the apostrophe), BOOL → TRUE/FALSE,
-- CMaybe nothing → NULL.
_ : rowInsert "acct" acctSchema (7 , 42 , "O'Brien" , false , nothing , tt) ≡
    "INSERT INTO \"acct\" (\"id\", \"tenant\", \"email\", \"verified\", \"revoked_at\") VALUES (7, 42, 'O''Brien', FALSE, NULL);"
_ = refl

_ : rowInsert "acct" acctSchema (7 , 42 , "a@b.com" , true , just 99 , tt) ≡
    "INSERT INTO \"acct\" (\"id\", \"tenant\", \"email\", \"verified\", \"revoked_at\") VALUES (7, 42, 'a@b.com', TRUE, 99);"
_ = refl

-- UPSERT = putT: insert-or-replace by pk; non-pk cols overwritten from EXCLUDED.
_ : rowUpsert "acct" acctSchema (7 , 42 , "a@b.com" , true , just 99 , tt) ≡
    "INSERT INTO \"acct\" (\"id\", \"tenant\", \"email\", \"verified\", \"revoked_at\") VALUES (7, 42, 'a@b.com', TRUE, 99) ON CONFLICT (\"id\") DO UPDATE SET \"tenant\"=EXCLUDED.\"tenant\", \"email\"=EXCLUDED.\"email\", \"verified\"=EXCLUDED.\"verified\", \"revoked_at\"=EXCLUDED.\"revoked_at\";"
_ = refl

_ : deleteById "acct" acctSchema 7 ≡ "DELETE FROM \"acct\" WHERE \"id\" = 7;"
_ = refl

-- conformant reads: result order is OURS (pk), never PG's physical order
_ : selectByNat "acct" acctSchema "tenant" 42
  ≡ "SELECT * FROM \"acct\" WHERE \"tenant\" = 42 ORDER BY \"id\""
_ = refl

_ : selectByStr "acct" acctSchema "email" "a@b.com"
  ≡ "SELECT * FROM \"acct\" WHERE \"email\" = 'a@b.com' ORDER BY \"id\""
_ = refl
