{-# OPTIONS --without-K #-}

-- Форматтер суммы ЮKassa (Агда-версия, зеркало Haskell fmtKop в YooKassa.agda).
--
-- Контракт — из OpenAPI-спеки ЮKassa (spec/yookassa-openapi.yaml,
-- components.schemas.MonetaryAmount.value): «Amount … always in fractional
-- form. The separator for the fractional part is a dot, no separator is used
-- for thousands.» — то есть копейки → "R.KK": целая часть без ведущих нулей
-- (кроме самого нуля), ровно две цифры после точки.
--
-- Вход типизирован (Ур.1): Positive — натуральное > 0 в минорных единицах;
-- ноль непредставим (mkPositive zero = nothing).
--
-- ─── Уровень 3 корректности ────────────────────────────────────────────────
-- fmt-safe: вывод fmtList НИКОГДА не содержит символов, враждебных JSON-телу
-- (сырых '"' и '\') — сумма вставляется в JSON-тело POST /payments, и её вывод
-- физически не может сломать строку/структуру тела.
--
-- Десятичные цифры берутся НЕ через stdlib `show` (для вывода show нет леммы
-- «только цифры»), а через digit10 : Fin 10 → Char — 10 литеральных кейсов, на
-- которых ¬quote/¬backslash доказывается бесплатно (редукция литералов).
-- Целая часть выводится сильной (well-founded) рекурсией по n > n / 10;
-- граница n / 10 < n выводится из m<n*o⇒m/o<n.
module Agdelte.Payment.YooKassaForm where

open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Nat using () renaming (_==_ to _==ℕ_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.String using (primStringFromList)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _/_; _%_; _<_; _≤_; z≤n; z<s; s<s)
open import Data.Nat.DivMod using (_mod_; m<n*o⇒m/o<n)
open import Data.Nat.Properties using (m<n+m; m<n⇒m<n*o; *-identityʳ; *-distribˡ-+
                                       ; *-comm)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; trans)

open import Data.Nat.Properties using (module ≤-Reasoning)
open ≤-Reasoning

------------------------------------------------------------------
-- Positive: сумма > 0 в минорных единицах (ноль непредставим)
------------------------------------------------------------------

data Positive : Set where
  posNat : (n : ℕ) → ¬ (n ≡ 0) → Positive

amountOf : Positive → ℕ
amountOf (posNat n _) = n

mkPositive : ℕ → Maybe Positive
mkPositive (suc n) = just (posNat (suc n) λ ())
mkPositive zero    = nothing

------------------------------------------------------------------
-- Десятичные цифры: литеральные кейсы (на них всё редуцируется)
------------------------------------------------------------------

digit10 : Fin 10 → Char
digit10 zero = '0'
digit10 (suc zero) = '1'
digit10 (suc (suc zero)) = '2'
digit10 (suc (suc (suc zero))) = '3'
digit10 (suc (suc (suc (suc zero)))) = '4'
digit10 (suc (suc (suc (suc (suc zero))))) = '5'
digit10 (suc (suc (suc (suc (suc (suc zero)))))) = '6'
digit10 (suc (suc (suc (suc (suc (suc (suc zero))))))) = '7'
digit10 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = '8'
digit10 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = '9'

------------------------------------------------------------------
-- Целая часть: десятичные цифры без ведущих нулей —
-- сильная рекурсия по n > n / 10
------------------------------------------------------------------

-- 0 < 9 * n при n > 0 (для m<n+m нужен хвост > 0)
0<9*n : ∀ m → 0 < suc m * 9
0<9*n m = m<n⇒m<n*o {n = suc m} 9 z<s

-- suc m < suc m * 10 (разложение suc m * (9 + 1))
*n10<n : ∀ m → suc m < suc m * 10
*n10<n m = begin-strict
  suc m                 <⟨ m<n+m (suc m) (0<9*n m) ⟩
  suc m * 9 + suc m     ≡⟨ sym (cong (suc m * 9 +_) (*-identityʳ (suc m))) ⟩
  suc m * 9 + suc m * 1 ≡⟨ sym (*-distribˡ-+ (suc m) 9 1) ⟩
  suc m * (9 + 1)       ≡⟨⟩
  suc m * 10            ∎

div10< : ∀ m → suc m / 10 < suc m
div10< m = m<n*o⇒m/o<n (*n10<n m)

------------------------------------------------------------------
-- Уровень 3: JSafe — нет сырых '"' и '\' в списке символов
------------------------------------------------------------------

data JBad : Char → Set where
  qch : JBad '"'
  bsl : JBad '\\'

data JSafe : List Char → Set where
  []   : JSafe []
  _∷_  : ∀ {c cs} → ¬ JBad c → JSafe cs → JSafe (c ∷ cs)

-- на литеральных цифрах/точке JBad непредставим (редукция литералов)
digit10-safe : ∀ (k : Fin 10) → ¬ JBad (digit10 k)
digit10-safe zero ()
digit10-safe (suc zero) ()
digit10-safe (suc (suc zero)) ()
digit10-safe (suc (suc (suc zero))) ()
digit10-safe (suc (suc (suc (suc zero)))) ()
digit10-safe (suc (suc (suc (suc (suc zero))))) ()
digit10-safe (suc (suc (suc (suc (suc (suc zero)))))) ()
digit10-safe (suc (suc (suc (suc (suc (suc (suc zero))))))) ()
digit10-safe (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ()
digit10-safe (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) ()

dot-safe : ¬ JBad '.'
dot-safe ()

safe-++ : ∀ xs ys → JSafe xs → JSafe ys → JSafe (xs ++ ys)
safe-++ []       ys _     q = q
safe-++ (x ∷ xs) ys (p ∷ px) q = p ∷ safe-++ xs ys px q

------------------------------------------------------------------
-- Целая часть: десятичные цифры n + доказательство JSafe — ОДНОЙ
-- сильной рекурсией по n > n / 10
------------------------------------------------------------------

-- zero → "0", ведущих нулей нет: при q = n / 10 = 0 хвост-«0» выбрасывается
-- (иначе «01» вместо «1» — ловили векторами)
digits' : (m : ℕ) → Acc _<_ m → Σ (List Char) JSafe
digits' zero _ = '0' ∷ [] , digit10-safe zero ∷ []
digits' (suc m) (acc rs) = step (suc m / 10) (suc m mod 10)
                                (digits' (suc m / 10) (rs (div10< m)))
  where
    step : (q : ℕ) (r : Fin 10) → Σ (List Char) JSafe → Σ (List Char) JSafe
    step zero    r (_ , _)     = digit10 r ∷ [] , digit10-safe r ∷ []
    step (suc k) r (cs , safe) =
      cs ++ digit10 r ∷ [] , safe-++ cs (digit10 r ∷ []) safe (digit10-safe r ∷ [])

digits : ℕ → List Char
digits n = proj₁ (digits' n (<-wellFounded n))

digits-safe : ∀ n → JSafe (digits n)
digits-safe n = proj₂ (digits' n (<-wellFounded n))

------------------------------------------------------------------
-- fmtList / fmtAmount: копейки → "R.KK" по MonetaryAmount.value
------------------------------------------------------------------

fmtList : Positive → List Char
fmtList p = digits (amountOf p / 100) ++ '.' ∷ digit10 (kop / 10 mod 10) ∷ digit10 (kop mod 10) ∷ []
  where
    kop = amountOf p % 100

fmtAmount : Positive → String
fmtAmount p = primStringFromList (fmtList p)

-- ГЛАВНАЯ ТЕОРЕМА модуля: вывод форматтера суммы JSON-безопасен
fmt-safe : ∀ (p : Positive) → JSafe (fmtList p)
fmt-safe p = safe-++ (digits (amountOf p / 100))
                     ('.' ∷ digit10 (kop / 10 mod 10) ∷ digit10 (kop mod 10) ∷ [])
                     (digits-safe (amountOf p / 100))
                     (dot-safe ∷ digit10-safe (kop / 10 mod 10)
                             ∷ digit10-safe (kop mod 10) ∷ [])
  where
    kop = amountOf p % 100
