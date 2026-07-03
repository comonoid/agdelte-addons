{-# OPTIONS --without-K #-}

-- Agdelte.Auth.RBAC.Typed — the MECHANISM for a domain to build its OWN privilege
-- system on the shared engine, type-safely. A domain supplies its Resource and Action
-- as Agda types (finite enums) + show functions; in return it gets typo-proof,
-- exhaustively-checked permission construction (`tperm Activity Cancel`) — no stringly-
-- typed mistakes at use sites. The resulting `Perm`s feed the generic engine unchanged.
--
-- Usage (in the domain):
--   data Res = Activity | …       data Act = Read | Cancel | …
--   open import Agdelte.Auth.RBAC.Typed
--   open Builder showRes showAct          -- now tperm/tAny/tcan are in scope, typed
--   operator = role "operator" (tperm Activity Cancel ∷ tAny Engagement ∷ []) …
module Agdelte.Auth.RBAC.Typed where

open import Agda.Builtin.String using (String)
open import Data.Bool using (Bool)
open import Data.List using (List)

open import Agdelte.Auth.RBAC using (Perm; perm; Policy; can)

-- Instantiate with a domain's Resource/Action enums + their show functions.
module Builder
  {Resource Action : Set}
  (showResource : Resource → String)
  (showAction   : Action   → String)
  where

  -- a typed permission
  tperm : Resource → Action → Perm
  tperm r a = perm (showResource r) (showAction a)

  -- all actions on a resource (resource-level wildcard)
  tAny : Resource → Perm
  tAny r = perm (showResource r) "*"

  -- typed authorization check
  tcan : Policy → List String → Resource → Action → Bool
  tcan pol roles r a = can pol roles (tperm r a)
