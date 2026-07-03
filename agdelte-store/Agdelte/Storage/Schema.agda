{-# OPTIONS --without-K #-}

-- Agdelte.Storage.Schema — declarative storage (docs/concepts/declarative-storage.md).
-- An entity is described once by a value-level Schema (ColTy/Column); the operational
-- machinery is DERIVED by interpreters over that schema — the same "reify structure,
-- derive behavior" pattern the reactive runtime uses (Node template → DOM). Today's
-- interpreters: the WAL codec (encodeRow/decodeRow) and SQL DDL (ddlOf). Tomorrow's
-- (CRUD, paging, Postgres) are more interpreters over the SAME schema, not rewrites.
--
-- The structure-preserving subset is enforced BY `ColTy`: it can only express atomic
-- domains, finite enums, nullable, and FK (= surrogate-key reference). Functions,
-- polymorphism, nested/irregular datatypes, existentials, codata cannot be expressed —
-- so a Schema is, by construction, storable AND relationally mappable. To EXTEND the
-- subset, add a ColTy constructor WITH all three interpretations (value-type ⟦_⟧, codec
-- enc/decAtom, sql sqlTy); without all three it is not structure-preserving (see §9.6).
module Agdelte.Storage.Schema where

open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Char using (primCharEquality)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_) renaming (map to lmap)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList) renaming (_++_ to _<>_)

open import Agdelte.Storage.Wire using
  ( R; lp; encℕ; decℕ; encStr; decStr; fieldR; _>>=R_; returnR; runR )

------------------------------------------------------------------------
-- The declarative core
------------------------------------------------------------------------

data ColTy : Set where
  CNat CStr CBool : ColTy
  CEnum  : ℕ → ColTy             -- finite nullary-sum (N variants), wire = decimal ordinal
  CEnumS : List String → ColTy   -- finite enum, wire = one of the given codes (by position);
                                  -- value = the ordinal (ℕ) ⇒ indexable + SQL SMALLINT
  CMaybe : ColTy → ColTy         -- nullable
  CFK    : String → ColTy        -- = CNat + reference to table T

record Column : Set where        -- `cindexed` ⇒ this column carries a secondary index
  constructor col
  field cname : String ; cty : ColTy ; cindexed : Bool
open Column public

mkCol : String → ColTy → Column  -- a plain (unindexed) column
mkCol n t = col n t false

-- A secondary index keys on the column's ℕ value (`keyOf`), so only ℕ-valued column
-- types are admissible. `isIndexable` lists them; the {T (isIndexable t)} guard on
-- `idxCol` turns `idxCol "x" CStr` / `… (CMaybe _)` into a COMPILE ERROR rather than a
-- silent all-keys-collide-to-0 bug. (`col` is the low-level constructor; prefer mkCol/idxCol.)
isIndexable : ColTy → Bool
isIndexable CNat       = true
isIndexable (CFK _)    = true
isIndexable (CEnum _)  = true
isIndexable (CEnumS _) = true
isIndexable CBool      = true
isIndexable CStr       = false
isIndexable (CMaybe _) = false

idxCol : (n : String) (t : ColTy) → {T (isIndexable t)} → Column
idxCol n t = col n t true

Schema : Set
Schema = List Column             -- first column = surrogate PK (by convention)

⟦_⟧ : ColTy → Set                -- a column's Agda value type
⟦ CNat ⟧     = ℕ
⟦ CStr ⟧     = String
⟦ CBool ⟧    = Bool
⟦ CEnum _ ⟧  = ℕ
⟦ CEnumS _ ⟧ = ℕ
⟦ CMaybe t ⟧ = Maybe ⟦ t ⟧
⟦ CFK _ ⟧    = ℕ

Row : Schema → Set               -- a row = heterogeneous product typed by the schema
Row []       = ⊤
Row (c ∷ cs) = ⟦ cty c ⟧ × Row cs

------------------------------------------------------------------------
-- Interpreter 1 — the WAL codec, derived from the schema
------------------------------------------------------------------------

private
  encBool : Bool → String
  encBool true  = "1"
  encBool false = "0"
  decBool : String → Bool
  decBool "1" = true
  decBool _   = false
  -- CEnumS: ordinal ↔ code string (the code list is the schema's variant set)
  nthS : List String → ℕ → String
  nthS []       _       = ""
  nthS (x ∷ _)  zero    = x
  nthS (_ ∷ xs) (suc n) = nthS xs n
  idxOfS : List String → String → Maybe ℕ
  idxOfS []       _ = nothing
  idxOfS (x ∷ xs) s = if primStringEquality x s then just zero else map suc (idxOfS xs s)

encAtom : (t : ColTy) → ⟦ t ⟧ → String
encAtom CNat        v        = encℕ v
encAtom CStr        v        = encStr v
encAtom CBool       v        = encBool v
encAtom (CEnum _)   v        = encℕ v
encAtom (CEnumS cs) v        = nthS cs v           -- ordinal → code (byte-identical to the codes)
encAtom (CFK _)     v        = encℕ v
encAtom (CMaybe t)  nothing  = "n"                 -- matches Wire.encMaybeℕ/Str
encAtom (CMaybe t)  (just x) = "j" <> encAtom t x

decAtom : (t : ColTy) → String → Maybe ⟦ t ⟧
decAtom CNat        = decℕ
decAtom CStr        = decStr
decAtom CBool s     = just (decBool s)
decAtom (CEnum _)   = decℕ
decAtom (CEnumS cs) s = idxOfS cs s                -- code → ordinal; unknown code ⇒ nothing (strict)
decAtom (CFK _)     = decℕ
decAtom (CMaybe t) s = goM (toList s)
  where goM : List Char → Maybe (Maybe ⟦ t ⟧)
        goM []         = just nothing
        goM (c ∷ rest) = if primCharEquality c 'j'
                         then map just (decAtom t (fromList rest))
                         else just nothing                       -- 'n' (or other) → nothing

encodeRow : (s : Schema) → Row s → String
encodeRow []       _        = ""
encodeRow (c ∷ cs) (v , vs) = lp (encAtom (cty c) v) <> encodeRow cs vs

decodeRowR : (s : Schema) → R (Row s)
decodeRowR []       = returnR tt
decodeRowR (c ∷ cs) = fieldR (decAtom (cty c)) >>=R λ v →
                      decodeRowR cs            >>=R λ vs →
                      returnR (v , vs)

decodeRow : (s : Schema) → String → Maybe (Row s)
decodeRow s = runR (decodeRowR s)

------------------------------------------------------------------------
-- Tier-1 schema evolution: tolerant decode (docs/concepts/schema-evolution.md)
--
-- A column appended at the END of a schema can be read off an OLD record (which
-- lacks it): when the wire input is exhausted, fill the remaining columns with
-- `defaultOf` instead of failing. Only `CMaybe _` is auto-defaultable (→ nothing),
-- so additive evolution is restricted to appending nullable columns. For a FULL
-- record the default never fires, so `decodeRowTolerant ≡ decodeRow` byte-for-byte.
------------------------------------------------------------------------

defaultOf : (t : ColTy) → Maybe ⟦ t ⟧      -- just d ⇒ d defaults a missing trailing column
defaultOf (CMaybe _) = just nothing
defaultOf CNat       = nothing
defaultOf CStr       = nothing
defaultOf CBool      = nothing
defaultOf (CEnum _)  = nothing
defaultOf (CEnumS _) = nothing
defaultOf (CFK _)    = nothing

-- like fieldR, but an EXHAUSTED input yields the default (consuming nothing) rather
-- than failing; a missing column with no default (nothing) still fails.
fieldOrDefaultR : ∀ {A} → Maybe A → (String → Maybe A) → R A
fieldOrDefaultR (just d) _   []       = just (d , [])
fieldOrDefaultR nothing  _   []       = nothing
fieldOrDefaultR _        dec (c ∷ cs) = fieldR dec (c ∷ cs)

decodeRowTolerantR : (s : Schema) → R (Row s)
decodeRowTolerantR []       = returnR tt
decodeRowTolerantR (c ∷ cs) = fieldOrDefaultR (defaultOf (cty c)) (decAtom (cty c)) >>=R λ v →
                              decodeRowTolerantR cs                                  >>=R λ vs →
                              returnR (v , vs)

decodeRowTolerant : (s : Schema) → String → Maybe (Row s)
decodeRowTolerant s = runR (decodeRowTolerantR s)

------------------------------------------------------------------------
-- Interpreter 2 — SQL DDL, derived from the SAME schema (Postgres path, deferred)
------------------------------------------------------------------------

sqlTy : ColTy → String
sqlTy CNat        = "BIGINT"
sqlTy CStr        = "TEXT"
sqlTy CBool       = "BOOLEAN"
sqlTy (CEnum _)   = "SMALLINT"
sqlTy (CEnumS _)  = "SMALLINT"
sqlTy (CMaybe t)  = sqlTy t
sqlTy (CFK _)     = "BIGINT"

private
  fkRef : ColTy → String
  fkRef (CFK t) = " REFERENCES " <> t
  fkRef _       = ""
  nullableOf : ColTy → String
  nullableOf (CMaybe _) = ""
  nullableOf _          = " NOT NULL"
  colDDL : Bool → Column → String        -- first column = PK
  colDDL first c =
    cname c <> " " <> sqlTy (cty c)
    <> (if first then " PRIMARY KEY" else nullableOf (cty c))
    <> fkRef (cty c)

ddlOf : String → Schema → String
ddlOf table []       = "CREATE TABLE " <> table <> " ()"
ddlOf table (c ∷ cs) = "CREATE TABLE " <> table <> " (" <> colDDL true c <> rest cs <> ")"
  where rest : Schema → String
        rest []       = ""
        rest (x ∷ xs) = ", " <> colDDL false x <> rest xs

------------------------------------------------------------------------
-- Interpreter 3 — secondary indexes, derived from the SAME schema
--
-- A column marked `idxCol` declares a secondary index. Its index-key is the
-- column's ℕ value (`keyOf`): CNat/CFK/CEnum/CEnumS project directly, CBool maps
-- to 0/1. `imIndexes schema toRow` produces exactly the `List (V → List ℕ)` that
-- IndexedMap.empty consumes — so a store's index maintenance is now DERIVED from
-- the schema, the same source that drives the codec and the DDL. Index POSITION =
-- order of idxCol columns in the schema (the domain's typed index-name ↦ position).
------------------------------------------------------------------------

keyOf : (t : ColTy) → ⟦ t ⟧ → ℕ      -- the ℕ index-key of an (indexable) column value
keyOf CNat       v = v
keyOf (CFK _)    v = v
keyOf (CEnum _)  v = v
keyOf (CEnumS _) v = v
keyOf CBool      v = if v then suc zero else zero
keyOf CStr       _ = zero             -- unreachable for real indexes: idxCol's guard rejects
keyOf (CMaybe _) _ = zero             -- non-ℕ columns; these clauses exist only for totality

-- one extractor per indexed column, in schema order, over the structured Row
indexExtractors : (s : Schema) → List (Row s → List ℕ)
indexExtractors []       = []
indexExtractors (c ∷ cs) =
  let rest = lmap (λ ext r → ext (proj₂ r)) (indexExtractors cs)
  in if cindexed c
     then (λ r → keyOf (cty c) (proj₁ r) ∷ []) ∷ rest
     else rest

-- adapt the Row-extractors to the stored entity via its toRow ⇒ ready for IndexedMap.empty
imIndexes : (s : Schema) → ∀ {V : Set} → (V → Row s) → List (V → List ℕ)
imIndexes s f = lmap (λ ext v → ext (f v)) (indexExtractors s)

-- the indexes also render to SQL (one CREATE INDEX per idxCol) from the same marks
indexDDLs : String → Schema → List String
indexDDLs table = go
  where go : Schema → List String
        go []       = []
        go (c ∷ cs) = if cindexed c
                      then ("CREATE INDEX ON " <> table <> " (" <> cname c <> ")") ∷ go cs
                      else go cs
