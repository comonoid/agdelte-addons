{-# OPTIONS --without-K #-}

-- form-urlencoded кодировщик (Агда-версия, зеркало Haskell formEnc в Stripe.agda).
--
-- Зачем: Agda-сторона платёжного клиента строит то же тело, что и Haskell-FFI;
-- зеркальные векторы в StripeTest гарантируют, что версии не разъезжаются
-- (включая кириллицу — баг «index too large» был именно тут).
--
-- Правила (RFC 3986 + x-www-form-urlencoded): неотэкранированными остаются
-- A-Z a-z 0-9 - _ . ~; всё остальное (включая ' ', '=', '&', '+', кириллицу,
-- сам '%') → %XX, две ЗАГЛАВНЫЕ hex-цифры.
module Agdelte.Payment.StripeForm where

open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.String using (primStringToList; primStringFromList)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Char using (Char; toℕ; fromℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; _+_; _/_; _%_)
open import Data.Nat.Properties using (_≤?_; _<?_; _≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)

private
  inRange : ℕ → ℕ → ℕ → Bool
  inRange lo hi n = ⌊ lo ≤? n ⌋ ∧ ⌊ n ≤? hi ⌋

  -- неотэкранируемые: 0-9 A-Z a-z - _ . ~
  unres? : ℕ → Bool
  unres? n =
    (inRange 48 57 n)
    ∨ (inRange 65 90 n)
    ∨ (inRange 97 122 n)
    ∨ ⌊ n ≟ 45 ⌋ ∨ ⌊ n ≟ 95 ⌋ ∨ ⌊ n ≟ 46 ⌋ ∨ ⌊ n ≟ 126 ⌋

  hexDigit : ℕ → Char
  hexDigit n = if ⌊ n <? 10 ⌋ then fromℕ (48 + n) else fromℕ (55 + n)

  -- байт 0..255 → '%', hex hi, hex lo
  encodeByte : ℕ → List Char
  encodeByte b = '%' ∷ hexDigit (b / 16) ∷ hexDigit (b % 16) ∷ []

  -- codepoint → UTF-8 байты (0..0x7F — 1 байт, до 0x7FF — 2, до 0xFFFF — 3)
  utf8 : ℕ → List ℕ
  utf8 n = if ⌊ n <? 128 ⌋ then n ∷ []
           else if ⌊ n <? 2048 ⌋ then (192 + n / 64) ∷ (128 + n % 64) ∷ []
           else (224 + n / 4096) ∷ (128 + (n / 64) % 64) ∷ (128 + n % 64) ∷ []

  encChar : Char → List Char
  encChar c = if unres? (toℕ c) then c ∷ [] else concatMap encodeByte (utf8 (toℕ c))
    where
      _++^_ : List Char → List Char → List Char
      [] ++^ ys = ys
      (x ∷ xs) ++^ ys = x ∷ (xs ++^ ys)

      concatMap : (ℕ → List Char) → List ℕ → List Char
      concatMap f [] = []
      concatMap f (b ∷ bs) = f b ++ concatMap f bs

      concat : List (List Char) → List Char
      concat [] = []
      concat (xs ∷ xss) = xs ++ concat xss

-- строка → закодированный список символов
formEncList : String → List Char
formEncList s = go (primStringToList s)
  where
    go : List Char → List Char
    go [] = []
    go (c ∷ cs) = encChar c ++ go cs

-- строка → строка (percent-encoded); НИКОГДА не содержит сырых ' ', '=', '&', '+'
formEncS : String → String
formEncS str = primStringFromList (formEncList str)
