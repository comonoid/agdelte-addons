{-# OPTIONS --without-K #-}

-- Agdelte.Auth.RBAC.Presets — the "simple path" facade. Lets a trivial deployment use
-- RBAC without ever touching Perm/Role records, hierarchy or SoD: roles are described
-- as plain string config and permissions are checked as "resource:action" strings. The
-- full engine is still underneath (progressive disclosure) — reach for RBAC directly
-- only when you need wildcards-in-roles, deep hierarchies or constraints.
module Agdelte.Auth.RBAC.Presets where

open import Agda.Builtin.String using (String)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; proj₁; proj₂)

open import Agdelte.Auth.RBAC
  using (Perm; perm; Role; role; Policy; can; parsePerm)

-- a flat role (no hierarchy) from "resource:action" permission strings
flatRole : String → List String → Role
flatRole rid perms = role rid (map parsePerm perms) []

-- a role with parents (string hierarchy)
roleH : (id : String) → (perms parents : List String) → Role
roleH rid perms parents = role rid (map parsePerm perms) parents

-- the all-powerful role (one line)
superAdmin : String → Role
superAdmin rid = role rid (perm "*" "*" ∷ []) []

-- a flat policy straight from config: [(roleName, ["res:act", …]), …]
policyOf : List (String × List String) → Policy
policyOf = map (λ p → flatRole (proj₁ p) (proj₂ p))

-- check a permission expressed as a string — the simple-case entry point
canStr : Policy → (subjectRoles : List String) → (need : String) → Bool
canStr pol roles need = can pol roles (parsePerm need)
