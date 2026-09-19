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

open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.Nat using () renaming (_==_ to _==ℕ_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.String using (primStringFromList)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Char using (toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _/_; _%_; _<_; _≤_; z≤n; z<s; s<s)
open import Data.Nat.DivMod using (_mod_; m%n<n; m<n⇒m%n≡m; m<n*o⇒m/o<n; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (m<n+m; m<n⇒m<n*o; +-comm; *-identityʳ; *-distribˡ-+
                                       ; *-comm)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans)

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
-- Целая часть: десятичные цифры n — ОДНА сильная рекурсия по n > n / 10,
-- несущая ВСЕ инварианты сразу: JSafe (нет '"' '\') и AllDigits (только
-- цифры — база round-trip-теоремы)
------------------------------------------------------------------

-- «Не точка»: редуцируемое сравнение с '.' (литералы считаютcя сразу)
IsDot : Char → Set
IsDot c = primCharEquality c '.' ≡ true

data AllDigits : List Char → Set where
  []   : AllDigits []
  _∷_  : ∀ c cs → ¬ IsDot c → AllDigits cs → AllDigits (c ∷ cs)

-- zero → "0", ведущих нулей нет: при q = n / 10 = 0 хвост-«0» выбрасывается
-- (иначе «01» вместо «1» — ловили векторами)
Digits = Σ (List Char) (λ cs → JSafe cs × AllDigits cs)

digit10-¬dot : ∀ (k : Fin 10) → ¬ IsDot (digit10 k)
digit10-¬dot zero = λ ()
digit10-¬dot (suc zero) = λ ()
digit10-¬dot (suc (suc zero)) = λ ()
digit10-¬dot (suc (suc (suc zero))) = λ ()
digit10-¬dot (suc (suc (suc (suc zero)))) = λ ()
digit10-¬dot (suc (suc (suc (suc (suc zero))))) = λ ()
digit10-¬dot (suc (suc (suc (suc (suc (suc zero)))))) = λ ()
digit10-¬dot (suc (suc (suc (suc (suc (suc (suc zero))))))) = λ ()
digit10-¬dot (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = λ ()
digit10-¬dot (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = λ ()

digit10-all : ∀ (k : Fin 10) → AllDigits (digit10 k ∷ [])
digit10-all k = _∷_ (digit10 k) [] (digit10-¬dot k) []

allDigits-++ : ∀ xs ys → AllDigits xs → AllDigits ys → AllDigits (xs ++ ys)
allDigits-++ [] ys _ q = q
allDigits-++ (x ∷ xs) ys (_∷_ .x .xs nd px) q = _∷_ x (xs ++ ys) nd (allDigits-++ xs ys px q)

private
  step : (q : ℕ) (r : Fin 10) → Digits → Digits
  step zero    r (_ , s , _) =
    digit10 r ∷ [] , digit10-safe r ∷ [] , digit10-all r
  step (suc k) r (cs , s , d) =
    cs ++ digit10 r ∷ []
    , safe-++ cs (digit10 r ∷ []) s (digit10-safe r ∷ [])
    , allDigits-++ cs (digit10 r ∷ []) d (digit10-all r)

digits' : (m : ℕ) → Acc _<_ m → Digits
digits' zero _ = '0' ∷ [] , digit10-safe zero ∷ [] , digit10-all zero
digits' (suc m) (acc rs) = step (suc m / 10) (suc m mod 10)
                                (digits' (suc m / 10) (rs (div10< m)))

digits : ℕ → List Char
digits n = proj₁ (digits' n (<-wellFounded n))

digits-safe : ∀ n → JSafe (digits n)
digits-safe n = proj₁ (proj₂ (digits' n (<-wellFounded n)))

digits-all : ∀ n → AllDigits (digits n)
digits-all n = proj₂ (proj₂ (digits' n (<-wellFounded n)))

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

------------------------------------------------------------------
-- Ур.3+: round-trip — parseAmount (fmtList p) ≡ amountOf p.
-- «Отформатировал → распарсил = та же сумма»: теорема закрывает класс
-- «цифры правильные, порядок перепутан» сильнее, чем векторы.
------------------------------------------------------------------

charDig : Char → ℕ
charDig c = toℕ c ∸ 48

-- литеральные кейсы: charDig цифры = значение Fin
digit10-val : ∀ (k : Fin 10) → charDig (digit10 k) ≡ Data.Fin.toℕ k
digit10-val zero = refl
digit10-val (suc zero) = refl
digit10-val (suc (suc zero)) = refl
digit10-val (suc (suc (suc zero))) = refl
digit10-val (suc (suc (suc (suc zero)))) = refl
digit10-val (suc (suc (suc (suc (suc zero))))) = refl
digit10-val (suc (suc (suc (suc (suc (suc zero)))))) = refl
digit10-val (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
digit10-val (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
digit10-val (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl

parseDigitsAcc : ℕ → List Char → ℕ
parseDigitsAcc st []       = st
parseDigitsAcc st (c ∷ cs) = parseDigitsAcc (st * 10 + charDig c) cs

parseDigits : List Char → ℕ
parseDigits = parseDigitsAcc 0

parseDigits-++1 : ∀ acc cs c →
  parseDigitsAcc acc (cs ++ c ∷ []) ≡ parseDigitsAcc (parseDigitsAcc acc cs) (c ∷ [])
parseDigits-++1 st []       c = refl
parseDigits-++1 st (x ∷ cs) c = parseDigits-++1 (st * 10 + charDig x) cs c

-- ядро: десятичные цифры m разбираются обратно в m
digits-roundtrip : ∀ m → parseDigits (digits m) ≡ m
digits-roundtrip m = help m (<-wellFounded m)
  where
    step-parse : ∀ (q : ℕ) (r : Fin 10) (d : Digits) →
                 parseDigits (proj₁ d) ≡ q →
                 parseDigits (proj₁ (step q r d)) ≡ q * 10 + charDig (digit10 r)
    step-parse zero r (_ , _ , _) ih = refl
    step-parse (suc k) r (cs , _ , _) ih = begin-equality
      parseDigits (cs ++ digit10 r ∷ [])        ≡⟨ parseDigits-++1 0 cs (digit10 r) ⟩
      parseDigits cs * 10 + charDig (digit10 r) ≡⟨ cong (λ a → a * 10 + charDig (digit10 r)) ih ⟩
      suc k * 10 + charDig (digit10 r)          ∎

    help : ∀ (n : ℕ) (a : Acc _<_ n) → parseDigits (proj₁ (digits' n a)) ≡ n
    help zero a = refl
    help (suc n) (acc rs) = begin-equality
      parseDigits (proj₁ (digits' (suc n) (acc rs)))                ≡⟨⟩
      parseDigits (proj₁ (step (suc n / 10) (suc n mod 10)
                                (digits' (suc n / 10) (rs (div10< n))))) ≡⟨ step-parse (suc n / 10) (suc n mod 10) (digits' (suc n / 10) (rs (div10< n))) (help (suc n / 10) (rs (div10< n))) ⟩
      (suc n / 10) * 10 + charDig (digit10 (suc n mod 10))           ≡⟨ cong ((suc n / 10) * 10 +_) (trans (digit10-val (suc n mod 10)) (toℕ-fromℕ< (m%n<n (suc n) 10))) ⟩
      (suc n / 10) * 10 + suc n % 10                                ≡⟨ m≡m%n+[m/n]*n-alternative ⟩
      suc n                                                         ∎
      where
        m≡m%n+[m/n]*n-alternative : (suc n / 10) * 10 + suc n % 10 ≡ suc n
        m≡m%n+[m/n]*n-alternative =
          trans (+-comm ((suc n / 10) * 10) (suc n % 10))
                (sym (m≡m%n+[m/n]*n (suc n) 10))

------------------------------------------------------------------
-- Разбор "R.KK" обратно в копейки
------------------------------------------------------------------

-- ВАЖНО: диспетч через Dec, а НЕ литеральным паттерном '.' — иначе go на
-- символьном char не редуцируется (клозы с литералом блокируют рекsурсию)
-- и round-trip-теорема не проходит конверсией.
go : ℕ → List Char → ℕ
go st [] = st
go st (c ∷ rest) with primCharEquality c '.'
... | true  = st * 100 + parseDigits rest
... | false = go (st * 10 + charDig c) rest

go-lemma : ∀ st c rest →
  go st (c ∷ rest) ≡ (if primCharEquality c '.' then st * 100 +
                      parseDigits rest else
                      go (st * 10 + charDig c) rest)
go-lemma st c rest with primCharEquality c '.'
go-lemma st c rest | true  = refl
go-lemma st c rest | false = refl

parseAmount : List Char → ℕ
parseAmount = go 0

-- на цифровом префиксе go ведёт себя как накопитель разрядов
go-digits++ : ∀ ds rest st → AllDigits ds → go st (ds ++ rest) ≡ go (go st ds) rest
go-digits++ [] rest st _ = refl
go-digits++ (c ∷ ds) rest st (_∷_ .c .ds nd d) with primCharEquality c '.'
... | true  = ⊥-elim (nd refl)
... | false rewrite go-lemma st c (ds ++ rest)
          | go-lemma st c ds
          | go-digits++ ds rest (st * 10 + charDig c) d = refl

go-parse : ∀ ds st → AllDigits ds → go st ds ≡ parseDigitsAcc st ds
go-parse [] st _ = refl
go-parse (c ∷ ds) st (_∷_ .c .ds nd d) with primCharEquality c '.'
... | true  = ⊥-elim (nd refl)
... | false rewrite go-lemma st c ds | go-parse ds (st * 10 + charDig c) d = refl

-- ГЛАВНАЯ ТЕОРЕМА 2 модуля
fmt-roundtrip : ∀ (p : Positive) → parseAmount (fmtList p) ≡ amountOf p
fmt-roundtrip p = begin-equality
  parseAmount (fmtList p)                                   ≡⟨⟩
  go 0 (digits rub ++ '.' ∷ kop2)                           ≡⟨ go-digits++ (digits rub) ('.' ∷ kop2) 0 (digits-all rub) ⟩
  go (go 0 (digits rub)) ('.' ∷ kop2)                       ≡⟨ cong (λ acc → go acc ('.' ∷ kop2)) (go-parse (digits rub) 0 (digits-all rub)) ⟩
  go (parseDigits (digits rub)) ('.' ∷ kop2)                ≡⟨ cong (λ acc → go acc ('.' ∷ kop2)) (digits-roundtrip rub) ⟩
  go rub ('.' ∷ kop2)                                       ≡⟨⟩
  rub * 100 + parseDigits kop2                              ≡⟨ cong (rub * 100 +_) (kop₂≡) ⟩
  rub * 100 + (kop / 10 * 10 + kop % 10)                    ≡⟨ cong (rub * 100 +_) (trans (+-comm (kop / 10 * 10) (kop % 10)) (sym (m≡m%n+[m/n]*n kop 10))) ⟩
  rub * 100 + kop                                           ≡⟨ trans (+-comm (rub * 100) kop) (sym (m≡m%n+[m/n]*n (amountOf p) 100)) ⟩
  amountOf p                                                ∎
  where
    kop  = amountOf p % 100
    rub  = amountOf p / 100
    kop2 = digit10 (kop / 10 mod 10) ∷ digit10 (kop mod 10) ∷ []
    kop10<10 : kop / 10 < 10
    kop10<10 = m<n*o⇒m/o<n (m%n<n (amountOf p) 100)
    kop₂≡ : parseDigits kop2 ≡ kop / 10 * 10 + kop % 10
    kop₂≡ =
      trans (cong₂ (λ a b → a * 10 + b)
                   (trans (digit10-val (kop / 10 mod 10))
                          (toℕ-fromℕ< (m%n<n (kop / 10) 10)))
                   (trans (digit10-val (kop mod 10))
                          (toℕ-fromℕ< (m%n<n kop 10))))
            (cong (λ a → a * 10 + kop % 10) (m<n⇒m%n≡m kop10<10))
