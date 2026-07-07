{-# OPTIONS --without-K #-}

-- Compile-time tests for the JSON→Row read path: exact decodes pinned by `refl` — escapes,
-- NULL→CMaybe, booleans, key-order robustness, \u-escaped Cyrillic, and rejection cases.
module Agdelte.Storage.JsonRowTest where

open import Agda.Builtin.Unit using (tt)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Storage.Schema using (Schema; mkCol; idxCol; CNat; CStr; CBool; CMaybe; CFK)
open import Agdelte.Storage.JsonRow using (decodeRows)

acct : Schema
acct = mkCol "id" CNat ∷ idxCol "tenant" (CFK "tenant") ∷ mkCol "email" CStr
     ∷ mkCol "verified" CBool ∷ mkCol "revoked_at" (CMaybe CNat) ∷ []

-- two rows: escaped quote in a string, NULL, true/false, a present CMaybe
_ : decodeRows acct
      "[{\"id\":7,\"tenant\":42,\"email\":\"O'Brien \\\"x\\\"\",\"verified\":false,\"revoked_at\":null},
        {\"id\":8,\"tenant\":42,\"email\":\"a@b.com\",\"verified\":true,\"revoked_at\":99}]"
  ≡ just ( (7 , 42 , "O'Brien \"x\"" , false , nothing , tt)
         ∷ (8 , 42 , "a@b.com" , true , just 99 , tt) ∷ [] )
_ = refl

-- key order in the JSON does not matter (lookup by column name)
_ : decodeRows acct
      "[{\"revoked_at\":null,\"email\":\"x@y\",\"id\":1,\"verified\":true,\"tenant\":2}]"
  ≡ just ((1 , 2 , "x@y" , true , nothing , tt) ∷ [])
_ = refl

-- \u-escaped BMP char (Cyrillic р) and a literal Cyrillic string both decode
_ : decodeRows acct
      "[{\"id\":1,\"tenant\":2,\"email\":\"\\u0440\\u0443с\",\"verified\":true,\"revoked_at\":null}]"
  ≡ just ((1 , 2 , "рус" , true , nothing , tt) ∷ [])
_ = refl

-- absent NON-nullable key ⇒ reject (only CMaybe tolerates absence)
_ : decodeRows acct "[{\"id\":1,\"tenant\":2,\"verified\":true,\"revoked_at\":null}]" ≡ nothing
_ = refl

-- absent CMaybe key ⇒ NULL
_ : decodeRows acct "[{\"id\":1,\"tenant\":2,\"email\":\"e\",\"verified\":false}]"
  ≡ just ((1 , 2 , "e" , false , nothing , tt) ∷ [])
_ = refl

-- type mismatch (string where nat expected) ⇒ reject
_ : decodeRows acct
      "[{\"id\":\"seven\",\"tenant\":2,\"email\":\"e\",\"verified\":true,\"revoked_at\":null}]" ≡ nothing
_ = refl

-- empty result set
_ : decodeRows acct "[]" ≡ just []
_ = refl

-- audit D2: a surrogate-pair escape decodes to the real character (😀 = U+1F600 = 😀);
-- a lone high surrogate is rejected as malformed
_ : decodeRows acct
      "[{\"id\":1,\"tenant\":2,\"email\":\"hi \\ud83d\\ude00\",\"verified\":true,\"revoked_at\":null}]"
  ≡ just ((1 , 2 , "hi 😀" , true , nothing , tt) ∷ [])
_ = refl

_ : decodeRows acct
      "[{\"id\":1,\"tenant\":2,\"email\":\"bad \\ud83d!\",\"verified\":true,\"revoked_at\":null}]"
  ≡ nothing
_ = refl
