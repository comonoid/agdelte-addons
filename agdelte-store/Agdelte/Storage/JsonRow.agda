{-# OPTIONS --without-K #-}

-- JSON → Row: the READ half of the schema codecs (pg-store-plan Ф0). `queryConn` returns a JSON
-- array of FLAT objects (one per row, scalar values only — exactly what PG row-to-JSON emits for
-- our schemas); this module parses that subset in PURE Agda (stdlib-only, so the store stays
-- self-contained) and converts each object into a typed `Row s` by column NAME (order-robust).
--
-- The parser is total via FUEL (input length bounds every loop) — no pragmas, no sized types.
-- Unsupported by design: nested objects/arrays (our rows are flat), negative numbers (all
-- columns are ℕ-backed). \u escapes cover the BMP AND surrogate pairs (audit D2: emoji in
-- community content survive an escaping JSON encoder); non-ASCII normally arrives as raw UTF-8.
module Agdelte.Storage.JsonRow where

open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Char using (Char; primCharToNat; primNatToChar; primCharEquality)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤ᵇ_; _<ᵇ_; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList; fromList)

open import Agdelte.Storage.Schema using
  ( Schema; Column; ColTy; CNat; CStr; CBool; CEnum; CEnumS; CMaybe; CFK
  ; cname; cty; ⟦_⟧; Row )

------------------------------------------------------------------------
-- Scalars (the only JSON values a flat row can hold)
------------------------------------------------------------------------

data Scalar : Set where
  sNat  : ℕ → Scalar
  sStr  : String → Scalar
  sBool : Bool → Scalar
  sNull : Scalar

private
  cn : Char → ℕ
  cn = primCharToNat

  isDigit : Char → Bool
  isDigit c = (47 <ᵇ cn c) ∧ (cn c <ᵇ 58)

  digit : Char → ℕ
  digit c = cn c ∸ 48

  hexVal : Char → Maybe ℕ
  hexVal c = if isDigit c then just (digit c)
             else if (96 <ᵇ cn c) ∧ (cn c <ᵇ 103) then just (cn c ∸ 87)   -- a-f
             else if (64 <ᵇ cn c) ∧ (cn c <ᵇ 71)  then just (cn c ∸ 55)   -- A-F
             else nothing

  isWs : Char → Bool
  isWs c = (cn c ≡ᵇ 32) ∨ (cn c ≡ᵇ 9) ∨ (cn c ≡ᵇ 10) ∨ (cn c ≡ᵇ 13)
    where open import Data.Nat using (_≡ᵇ_)

  ws : List Char → List Char
  ws [] = []
  ws (c ∷ cs) = if isWs c then ws cs else c ∷ cs

  -- number: 1+ digits (accumulate; structural)
  nat : ℕ → List Char → Maybe (ℕ × List Char)
  nat acc []       = just (acc , [])
  nat acc (c ∷ cs) = if isDigit c then nat (acc * 10 + digit c) cs else just (acc , c ∷ cs)

  -- string body after the opening quote; structural on chars (escape = consume ≥2)
  str : List Char → List Char → Maybe (String × List Char)
  str acc [] = nothing
  str acc ('"' ∷ cs) = just (fromList (reverse acc) , cs)
  str acc ('\\' ∷ 'n' ∷ cs) = str ('\n' ∷ acc) cs
  str acc ('\\' ∷ 't' ∷ cs) = str ('\t' ∷ acc) cs
  str acc ('\\' ∷ 'r' ∷ cs) = str ('\r' ∷ acc) cs
  str acc ('\\' ∷ 'b' ∷ cs) = str (primNatToChar 8 ∷ acc) cs
  str acc ('\\' ∷ 'f' ∷ cs) = str (primNatToChar 12 ∷ acc) cs
  str acc ('\\' ∷ '"' ∷ cs) = str ('"' ∷ acc) cs
  str acc ('\\' ∷ '\\' ∷ cs) = str ('\\' ∷ acc) cs
  str acc ('\\' ∷ '/' ∷ cs) = str ('/' ∷ acc) cs
  str acc ('\\' ∷ 'u' ∷ a ∷ b ∷ c ∷ d ∷ cs) = withHex (hex4 a b c d) cs
    where
      hex4 : Char → Char → Char → Char → Maybe ℕ
      hex4 a′ b′ c′ d′ with hexVal a′ | hexVal b′ | hexVal c′ | hexVal d′
      ... | just x | just y | just z | just w = just (((x * 16 + y) * 16 + z) * 16 + w)
      ... | _ | _ | _ | _ = nothing
      isHigh isLow : ℕ → Bool                          -- UTF-16 surrogate ranges
      isHigh u = (55295 <ᵇ u) ∧ (u <ᵇ 56320)           -- D800..DBFF
      isLow  u = (56319 <ᵇ u) ∧ (u <ᵇ 57344)           -- DC00..DFFF
      withHex : Maybe ℕ → List Char → Maybe (String × List Char)
      withHex nothing  _    = nothing
      withHex (just u) rest =
        if isHigh u then lowHalf rest                  -- audit D2: combine the surrogate PAIR
        else if isLow u then nothing                   -- lone low surrogate: malformed
        else str (primNatToChar u ∷ acc) rest
        where
          lowHalf : List Char → Maybe (String × List Char)
          lowHalf ('\\' ∷ 'u' ∷ e ∷ f ∷ g ∷ h ∷ rest₂) with hex4 e f g h
          ... | just lo = if isLow lo
                          then str (primNatToChar (65536 + (u ∸ 55296) * 1024 + (lo ∸ 56320)) ∷ acc) rest₂
                          else nothing
          ... | nothing = nothing
          lowHalf _ = nothing
  str acc ('\\' ∷ _) = nothing
  str acc (c ∷ cs) = str (c ∷ acc) cs

  -- one scalar (whitespace already skipped)
  scalar : List Char → Maybe (Scalar × List Char)
  scalar ('"' ∷ cs) with str [] cs
  ... | just (s , rest) = just (sStr s , rest)
  ... | nothing         = nothing
  scalar ('t' ∷ 'r' ∷ 'u' ∷ 'e' ∷ cs)         = just (sBool true , cs)
  scalar ('f' ∷ 'a' ∷ 'l' ∷ 's' ∷ 'e' ∷ cs)   = just (sBool false , cs)
  scalar ('n' ∷ 'u' ∷ 'l' ∷ 'l' ∷ cs)         = just (sNull , cs)
  scalar (c ∷ cs) = if isDigit c then wrap (nat (digit c) cs) else nothing
    where wrap : Maybe (ℕ × List Char) → Maybe (Scalar × List Char)
          wrap (just (n , rest)) = just (sNat n , rest)
          wrap nothing           = nothing
  scalar [] = nothing

  Obj : Set
  Obj = List (String × Scalar)

  -- "key": scalar
  pair : List Char → Maybe ((String × Scalar) × List Char)
  pair cs with ws cs
  ... | ('"' ∷ cs₁) with str [] cs₁
  ...   | just (k , cs₂) with ws cs₂
  ...     | (':' ∷ cs₃) with scalar (ws cs₃)
  ...       | just (v , cs₄) = just ((k , v) , cs₄)
  ...       | nothing        = nothing
  pair cs | ('"' ∷ cs₁) | just (k , cs₂) | _ = nothing
  pair cs | ('"' ∷ cs₁) | nothing = nothing
  pair cs | _ = nothing

  -- gas-fuelled loops (each iteration consumes ≥1 char, so `length input` bounds them)
  pairs : ℕ → Obj → List Char → Maybe (Obj × List Char)
  pairs zero _ _ = nothing
  pairs (suc g) acc cs with pair cs
  ... | nothing = nothing
  ... | just (kv , cs₁) with ws cs₁
  ...   | (',' ∷ cs₂) = pairs g (kv ∷ acc) cs₂
  ...   | ('}' ∷ cs₂) = just (reverse (kv ∷ acc) , cs₂)
  ...   | _           = nothing

  object : ℕ → List Char → Maybe (Obj × List Char)
  object g cs with ws cs
  ... | ('{' ∷ cs₁) with ws cs₁
  ...   | ('}' ∷ cs₂) = just ([] , cs₂)
  ...   | cs₂         = pairs g [] cs₂
  object g cs | _ = nothing

  objects : ℕ → List Obj → List Char → Maybe (List Obj × List Char)
  objects zero _ _ = nothing
  objects (suc g) acc cs with object g cs
  ... | nothing = nothing
  ... | just (o , cs₁) with ws cs₁
  ...   | (',' ∷ cs₂) = objects g (o ∷ acc) cs₂
  ...   | (']' ∷ cs₂) = just (reverse (o ∷ acc) , cs₂)
  ...   | _           = nothing

-- the top parser: a JSON array of flat objects
parseRows : String → Maybe (List Obj)
parseRows s with ws (toList s)
... | ('[' ∷ cs) with ws cs
...   | (']' ∷ _) = just []
...   | cs₁ with objects (suc (length cs₁)) [] cs₁
...     | just (os , _) = just os
...     | nothing       = nothing
parseRows s | _ = nothing

------------------------------------------------------------------------
-- Object → typed Row (by column NAME — robust to column order in the JSON)
------------------------------------------------------------------------

private
  lookupO : String → Obj → Maybe Scalar
  lookupO k [] = nothing
  lookupO k ((k′ , v) ∷ o) = if primStringEquality k k′ then just v else lookupO k o

  convert : (t : ColTy) → Scalar → Maybe ⟦ t ⟧
  convert CNat       (sNat n)  = just n
  convert (CFK _)    (sNat n)  = just n
  convert (CEnum _)  (sNat n)  = just n
  convert (CEnumS _) (sNat n)  = just n
  convert CStr       (sStr s)  = just s
  convert CBool      (sBool b) = just b
  convert (CMaybe t) sNull     = just nothing
  convert (CMaybe t) v with convert t v
  ... | just x  = just (just x)
  ... | nothing = nothing
  convert _ _ = nothing

-- absent key ≡ sNull: `convert` then accepts it only for CMaybe (NULL) and rejects elsewhere
rowFromObj : (s : Schema) → Obj → Maybe (Row s)
rowFromObj [] _ = just _
rowFromObj (c ∷ cs) o with convert (cty c) (fromMaybe sNull (lookupO (cname c) o))
... | nothing = nothing
... | just x with rowFromObj cs o
...   | just r  = just (x , r)
...   | nothing = nothing

-- id-only decode (for index lookups compiled as `SELECT "id" …`): each object's "id" value
decodeIds : String → Maybe (List ℕ)
decodeIds j with parseRows j
... | nothing = nothing
... | just os = go os
  where
    idOf : Obj → Maybe ℕ
    idOf o with lookupO "id" o
    ... | just (sNat n) = just n
    ... | _             = nothing
    go : List Obj → Maybe (List ℕ)
    go [] = just []
    go (o ∷ os′) with idOf o | go os′
    ... | just n | just ns = just (n ∷ ns)
    ... | _      | _       = nothing

-- a single aggregate scalar (COUNT/SUM…): the named ℕ field of the FIRST object of the result
-- (e.g. `[{"count":3}]` → just 3). nothing = empty result / missing / non-ℕ field.
decodeFirstNat : String → String → Maybe ℕ
decodeFirstNat col j with parseRows j
... | nothing        = nothing
... | just []        = nothing
... | just (o ∷ _) with lookupO col o
...   | just (sNat n) = just n
...   | _             = nothing

-- the surrogate pk of a typed row = its FIRST column (by Schema convention), when ℕ-valued
rowPk : (s : Schema) → Row s → Maybe ℕ
rowPk []      _        = nothing
rowPk (c ∷ _) (v , _)  = pk (cty c) v
  where pk : (t : ColTy) → ⟦ t ⟧ → Maybe ℕ
        pk CNat    n = just n
        pk (CFK _) n = just n
        pk _       _ = nothing

-- the full read path: queryConn's JSON → typed rows
decodeRows : (s : Schema) → String → Maybe (List (Row s))
decodeRows s j with parseRows j
... | nothing = nothing
... | just os = go os
  where go : List Obj → Maybe (List (Row s))
        go [] = just []
        go (o ∷ os′) with rowFromObj s o | go os′
        ... | just r | just rs = just (r ∷ rs)
        ... | _      | _       = nothing