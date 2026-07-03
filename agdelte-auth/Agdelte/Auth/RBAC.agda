{-# OPTIONS --without-K #-}

-- Agdelte.Auth.RBAC — a full, DATA-DRIVEN role-based access control engine
-- (authorization). Roles, permissions and the hierarchy are values (loadable from
-- config/DB at runtime), NOT a compiled enum — so deployments define their own roles
-- without recompiling. Pure (stdlib only) ⇒ fully unit-testable and JS+GHC safe.
--
-- Model (covers NIST RBAC0+1+2):
--   * Perm     = resource × action, with "*" wildcard on either field;
--   * Role     = id + direct grants + inherited role ids (RBAC1 hierarchy);
--   * Policy   = the role catalogue; effectivePerms resolves inheritance transitively
--                and is cycle-safe (fuel-bounded by the policy size);
--   * can      = does a subject holding these roles have the needed permission;
--   * SoD      = separation-of-duty constraints (mutually-exclusive roles) + a
--                validity check on a role assignment (RBAC2).
--
-- Authn-agnostic: `can` takes the subject's role ids as input. HOW those are obtained
-- (JWT claims, session, …) is the authentication concern, wired in Middleware later.
module Agdelte.Auth.RBAC where

open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; concatMap; length; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Char using (Char)
open import Data.String using (toList; fromList) renaming (_++_ to _<>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

infix 7 _==ˢ_   -- bind tighter than ∧ (6) / ∨ (5)
_==ˢ_ : String → String → Bool
a ==ˢ b = primStringEquality a b

anyB : ∀ {A : Set} → (A → Bool) → List A → Bool
anyB p []       = false
anyB p (x ∷ xs) = p x ∨ anyB p xs

elemˢ : String → List String → Bool
elemˢ x = anyB (_==ˢ x)

------------------------------------------------------------------------
-- Permissions (resource × action; "*" = wildcard)
------------------------------------------------------------------------

record Perm : Set where
  constructor perm
  field
    resource : String
    action   : String
open Perm public

-- a GRANTED perm covers a NEEDED perm (wildcards apply on the granted side)
covers : (granted needed : Perm) → Bool
covers g n =
  (resource g ==ˢ "*" ∨ resource g ==ˢ resource n) ∧
  (action   g ==ˢ "*" ∨ action   g ==ˢ action   n)

showPerm : Perm → String
showPerm p = resource p <> ":" <> action p

-- parse "resource:action" (everything after the first ':' is the action)
parsePerm : String → Perm
parsePerm s = split (toList s) []
  where
    split : List Char → List Char → Perm
    split []        acc = perm (fromList (rev acc [])) "*"   -- no ':' → action = "*"
      where rev : List Char → List Char → List Char
            rev []       a = a
            rev (c ∷ cs) a = rev cs (c ∷ a)
    split (c ∷ cs) acc =
      if primCharEquality c ':'
      then perm (fromList (rev acc [])) (fromList cs)
      else split cs (c ∷ acc)
      where rev : List Char → List Char → List Char
            rev []       a = a
            rev (x ∷ xs) a = rev xs (x ∷ a)

------------------------------------------------------------------------
-- Roles, policy, and inheritance resolution (cycle-safe)
------------------------------------------------------------------------

record Role : Set where
  constructor role
  field
    roleId   : String
    grants   : List Perm
    inherits : List String     -- parent role ids
open Role public

Policy : Set
Policy = List Role

lookupRole : Policy → String → Maybe Role
lookupRole []       _   = nothing
lookupRole (r ∷ rs) rid = if roleId r ==ˢ rid then just r else lookupRole rs rid

-- effective perms of a role id = its grants ∪ those of every (transitively) inherited
-- role. Fuel-bounded by the policy size, so a (mis)configured inheritance cycle is
-- total (it just stops) rather than looping forever.
private
  effFuel : ℕ → Policy → String → List Perm
  effFuel zero    _   _   = []
  effFuel (suc f) pol rid with lookupRole pol rid
  ... | nothing = []
  ... | just r  = grants r ++ concatMap (effFuel f pol) (inherits r)

effectivePerms : Policy → String → List Perm
effectivePerms pol = effFuel (suc (length pol)) pol

------------------------------------------------------------------------
-- The authorization check
------------------------------------------------------------------------

-- does a single role (transitively) grant `need`?
roleCan : Policy → String → Perm → Bool
roleCan pol rid need = anyB (λ g → covers g need) (effectivePerms pol rid)

-- does a subject holding `roles` have permission `need`?
can : Policy → (subjectRoles : List String) → (need : Perm) → Bool
can pol roles need = anyB (λ rid → roleCan pol rid need) roles

------------------------------------------------------------------------
-- Separation of duty (RBAC2): mutually-exclusive roles
------------------------------------------------------------------------

SoD : Set
SoD = List (String × String)     -- pairs that must not be held together

-- does the assignment hold both members of some SoD pair?
violatesSoD : SoD → (roles : List String) → Bool
violatesSoD sod roles =
  anyB (λ pr → elemˢ (proj₁ pr) roles ∧ elemˢ (proj₂ pr) roles) sod

assignmentValid : SoD → (roles : List String) → Bool
assignmentValid sod roles = not (violatesSoD sod roles)
