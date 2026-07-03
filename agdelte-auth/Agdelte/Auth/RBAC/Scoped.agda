{-# OPTIONS --without-K #-}

-- Agdelte.Auth.RBAC.Scoped — scoped permissions + delegated administration (ARBAC):
-- "a user may manage privileges on THEIR OWN part". A subject holds roles WITHIN a
-- scope (a "/"-separated path, e.g. "ws/42"); a grant in scope S covers any subtree
-- "S/…". `canOn` answers "may the subject do `need` on a target scope". Delegation =
-- the meta-permission `role:assign`: an owner with it in a covering scope may assign
-- roles inside their subtree.
--
-- The base `Perm`/`Role`/`Policy` stay simple (unscoped) — scoping is this additive
-- layer, so simple deployments never pay for it. The assignment store (who holds which
-- role WHERE) is DOMAIN state (a CRM entity); this module only provides the checks.
module Agdelte.Auth.RBAC.Scoped where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Char using (Char)
open import Data.String using (toList) renaming (_++_ to _<>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Auth.RBAC using (Perm; perm; Policy; roleCan; _==ˢ_; anyB)

Scope : Set
Scope = String

------------------------------------------------------------------------
-- Scope covering: a granted scope covers a target iff the target equals it or
-- lies in its subtree ("ws/42" covers "ws/42" and "ws/42/x", but NOT "ws/420").
------------------------------------------------------------------------

private
  isPrefix : List Char → List Char → Bool      -- isPrefix p s = does s start with p
  isPrefix []       _        = true
  isPrefix (_ ∷ _)  []       = false
  isPrefix (x ∷ xs) (y ∷ ys) = primCharEquality x y ∧ isPrefix xs ys

-- "" and "*" are the GLOBAL scope (cover everything); otherwise equal-or-subtree.
scopeCovers : (granted target : Scope) → Bool
scopeCovers g t =
  (g ==ˢ "*") ∨ (g ==ˢ "") ∨ (g ==ˢ t) ∨ isPrefix (toList (g <> "/")) (toList t)

------------------------------------------------------------------------
-- Scoped assignment + checks
------------------------------------------------------------------------

-- the subject holds role `roleId` within `scope`
ScopedRoles : Set
ScopedRoles = List (String × Scope)      -- (roleId , scope)

-- may the subject perform `need` on `target` scope?
canOn : Policy → ScopedRoles → (need : Perm) → (target : Scope) → Bool
canOn pol srs need target =
  anyB (λ sr → scopeCovers (proj₂ sr) target ∧ roleCan pol (proj₁ sr) need) srs

-- delegated administration: may the subject ASSIGN roles within `target`?
-- (modeled as holding the `role:assign` meta-permission in a covering scope)
assignPerm : Perm
assignPerm = perm "role" "assign"

canAssign : Policy → ScopedRoles → (target : Scope) → Bool
canAssign pol srs target = canOn pol srs assignPerm target
