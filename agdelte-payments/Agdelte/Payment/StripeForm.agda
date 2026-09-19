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
--
-- ─── Уровень 3 корректности ────────────────────────────────────────────────
-- formEnc-safe: вывод formEncList НИКОГДА не содержит сырых ' ' '=' '&' '+'
-- (закодированное тело можно безболезненно вставить в key=value&key=value:
-- разделители не поломаются).
--
-- hex-цифры берутся НЕ через fromℕ (в stdlib нет леммы toℕ (fromℕ n) ≡ n для
-- Char), а через toHex : Fin 16 → Char — 16 литеральных кейсов, на которых
-- ¬Sep доказывается бесплатно (редукция литералов + toℕ литерала). Байты несут
-- доказательство < 256 (Byte = Σ ℕ (_< 256)); границы выводятся из
-- m<n*o⇒m/o<n и m%n<n (Data.Nat.DivMod).
--
-- ГРАНИЦА ТЕОРЕМЫ (честно): для codepoint'ов ≥ 0x400000 энкодер идёт по
-- legacy-пути, и Safe на них не распространяется — это ВНЕ реального
-- Unicode (весь Unicode < 0x110000). Астральная плоскость (эмодзи,
-- 0x10000..0x10FFFF) с версии фикса идёт по ЧЕСТНОМУ 4-байтовому UTF-8
-- (utf8B4), совпадающему с Haskell, и входит в теорему. Гипотеза WFList:
-- все символы строки < 0x400000 — т.е. весь реальный Unicode с запасом.
module Agdelte.Payment.StripeForm where

open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.String using (primStringToList; primStringFromList)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Char using (Char; toℕ; fromℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin as F using (Fin; fromℕ<)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _/_; _%_; _<_; z<s; s<s)
open import Data.Nat.DivMod using (m%n<n; m<n*o⇒m/o<n)
open import Data.Nat.Properties using (_≤?_; _<?_; _≟_; m≤n+m; <-trans; +-monoʳ-<)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; inspect)

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

  ------------------------------------------------------------------
  -- Доказательный слой: hex-цифры по Fin 16, байты по построению < 256
  ------------------------------------------------------------------

  -- 16 литеральных кейсов — на литералах всё редуцируется.
  toHex : Fin 16 → Char
  toHex F.zero          = '0'
  toHex (F.suc F.zero)  = '1'
  toHex (F.suc (F.suc F.zero))  = '2'
  toHex (F.suc (F.suc (F.suc F.zero)))  = '3'
  toHex (F.suc (F.suc (F.suc (F.suc F.zero))))  = '4'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))  = '5'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))  = '6'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))  = '7'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))  = '8'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))  = '9'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))))  = 'A'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))))  = 'B'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))))))  = 'C'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))))))  = 'D'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))))))))  = 'E'
  toHex (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))))))))  = 'F'

  -- байт с доказанной границей
  Byte = Σ ℕ (λ b → b < 256)

  -- байт 0..255 → '%', hex hi, hex lo
  encodeByteB : Byte → List Char
  encodeByteB (b , b<256) =
    '%' ∷ toHex (fromℕ< q<16) ∷ toHex (fromℕ< r<16) ∷ []
    where
      q<16 : b / 16 < 16
      q<16 = m<n*o⇒m/o<n b<256            -- b < 16 * 16 = 256

      r<16 : b % 16 < 16
      r<16 = m%n<n b 16

  -- codepoint < 0x10000 → UTF-8 байты по построению < 256 (те же формулы,
  -- что в legacy utf8 ниже; совпадение вывода проверяют зеркальные тесты)
  utf8B : (n : ℕ) → n < 65536 → List Byte
  utf8B n n<65536 with n <? 128
  ... | yes p<128 = (n , n<256) ∷ []
    where
      n<256 : n < 256
      n<256 = <-trans p<128 (s<s (m≤n+m 128 127))       -- n < 128 < 256
  ... | no _ with n <? 2048
  ...   | yes p<2048 = b1 ∷ b2 ∷ []
    where
      q<64 : n / 64 < 64
      q<64 = m<n*o⇒m/o<n (<-trans p<2048 (s<s (m≤n+m 2048 2047)))  -- n < 4096 = 64*64
      r<64 : n % 64 < 64
      r<64 = m%n<n n 64
      b1 : Byte
      b1 = 192 + n / 64 , +-monoʳ-< 192 q<64            -- 192+q < 192+64 = 256
      b2 : Byte
      b2 = 128 + n % 64 , <-trans (+-monoʳ-< 128 r<64) (s<s (m≤n+m 192 63))
      -- 128+r < 128+64 = 192 < 256
  ...   | no _ = b1 ∷ b2 ∷ b3 ∷ []
    where
      q1<16 : n / 4096 < 16
      q1<16 = m<n*o⇒m/o<n n<65536                       -- n < 16 * 4096 = 65536
      q2<64 : (n / 64) % 64 < 64
      q2<64 = m%n<n (n / 64) 64
      r<64 : n % 64 < 64
      r<64 = m%n<n n 64
      b1 : Byte
      b1 = 224 + n / 4096 , <-trans (+-monoʳ-< 224 q1<16) (s<s (m≤n+m 240 15))
      -- 224+q < 224+16 = 240 < 256
      b2 : Byte
      b2 = 128 + (n / 64) % 64 , <-trans (+-monoʳ-< 128 q2<64) (s<s (m≤n+m 192 63))
      b3 : Byte
      b3 = 128 + n % 64 , <-trans (+-monoʳ-< 128 r<64) (s<s (m≤n+m 192 63))

  ------------------------------------------------------------------
  -- 4-байтовая ветка (астральная плоскость): ФИКС — раньше codepoints
  -- ≥ 0x10000 шли по legacy 3-байтовому пути (расхождение с Haskell,
  -- известный баг); теперь честный 4-байтовый UTF-8, совпадающий с ним
  ------------------------------------------------------------------

  utf8B4 : (n : ℕ) → n < 4194304 → List Byte
  utf8B4 n n<4M =
    b1 ∷ b2 ∷ b3 ∷ b4 ∷ []
    where
      q0<16 : n / 262144 < 16
      q0<16 = m<n*o⇒m/o<n n<4M               -- n < 16 * 262144 = 4194304
      q1<64 : (n / 4096) % 64 < 64
      q1<64 = m%n<n (n / 4096) 64
      q2<64 : (n / 64) % 64 < 64
      q2<64 = m%n<n (n / 64) 64
      r<64 : n % 64 < 64
      r<64 = m%n<n n 64
      b1 : Byte
      b1 = 240 + n / 262144 , +-monoʳ-< 240 q0<16        -- 240 + q0 < 240 + 16 = 256
      b2 : Byte
      b2 = 128 + (n / 4096) % 64 , <-trans (+-monoʳ-< 128 q1<64) (s<s (m≤n+m 192 63))
      b3 : Byte
      b3 = 128 + (n / 64) % 64 , <-trans (+-monoʳ-< 128 q2<64) (s<s (m≤n+m 192 63))
      b4 : Byte
      b4 = 128 + n % 64 , <-trans (+-monoʳ-< 128 r<64) (s<s (m≤n+m 192 63))

  ------------------------------------------------------------------
  -- Legacy (ℕ-путь) — только fallback для codepoints ≥ 0x400000
  -- (вне реального Unicode, см. WFList ниже); в Safe-теорему не входит
  ------------------------------------------------------------------

  hexDigit : ℕ → Char
  hexDigit n = if ⌊ n <? 10 ⌋ then fromℕ (48 + n) else fromℕ (55 + n)

  encodeByte : ℕ → List Char
  encodeByte b = '%' ∷ hexDigit (b / 16) ∷ hexDigit (b % 16) ∷ []

  utf8 : ℕ → List ℕ
  utf8 n = if ⌊ n <? 128 ⌋ then n ∷ []
           else if ⌊ n <? 2048 ⌋ then (192 + n / 64) ∷ (128 + n % 64) ∷ []
           else (224 + n / 4096) ∷ (128 + (n / 64) % 64) ∷ (128 + n % 64) ∷ []

  cat : List (List Char) → List Char
  cat [] = []
  cat (xs ∷ xss) = xs ++ cat xss

  encCharB : Bool → Char → List Char
  encCharB true  c = c ∷ []
  encCharB false c with toℕ c <? 65536
  ...   | yes p = cat (map encodeByteB (utf8B (toℕ c) p))
  ...   | no _ with toℕ c <? 4194304
  ...     | yes q = cat (map encodeByteB (utf8B4 (toℕ c) q))   -- честный 4-байтовый UTF-8
  ...     | no  _ = cat (map encodeByte (utf8 (toℕ c)))        -- вне Unicode: fallback, см. шапку

  encChar : Char → List Char
  encChar c = encCharB (unres? (toℕ c)) c

  go : List Char → List Char
  go [] = []
  go (c ∷ cs) = encChar c ++ go cs

-- строка → закодированный список символов
formEncList : String → List Char
formEncList s = go (primStringToList s)

-- строка → строка (percent-encoded); НИКОГДА не содержит сырых ' ', '=', '&', '+'
formEncS : String → String
formEncS str = primStringFromList (formEncList str)

------------------------------------------------------------------
-- Безопасность: Safe = «нет сырых ' ' '=' '&' '+'»
------------------------------------------------------------------

private
  IsSep : Char → Set
  IsSep c = (c ≡ '=') ⊎ ((c ≡ '&') ⊎ ((c ≡ ' ') ⊎ (c ≡ '+')))

  data Safe : List Char → Set where
    []    : Safe []
    _∷_   : ∀ {c cs} → ¬ IsSep c → Safe cs → Safe (c ∷ cs)

  data Safe² : List (List Char) → Set where
    []    : Safe² []
    _∷_   : ∀ {xs xss} → Safe xs → Safe² xss → Safe² (xs ∷ xss)

  -- универсальный приём: у сепараторов коды 61/38/32/43, у литерала — свой
  ¬sep≠ : ∀ c → toℕ c ≢ 61 → toℕ c ≢ 38 → toℕ c ≢ 32 → toℕ c ≢ 43 → ¬ IsSep c
  ¬sep≠ c h= h& hsp h+ (inj₁ p)                = h=  (cong toℕ p)
  ¬sep≠ c h= h& hsp h+ (inj₂ (inj₁ p))         = h&  (cong toℕ p)
  ¬sep≠ c h= h& hsp h+ (inj₂ (inj₂ (inj₁ p)))  = hsp (cong toℕ p)
  ¬sep≠ c h= h& hsp h+ (inj₂ (inj₂ (inj₂ p)))  = h+  (cong toℕ p)

  bool≢ : true ≢ false
  bool≢ ()

  -- неотэкранируемый символ — не сепаратор (unres? 61/38/32/43 редуцируются в false)
  unres-¬sep : ∀ c → unres? (toℕ c) ≡ true → ¬ IsSep c
  unres-¬sep c eq (inj₁ p) =
    bool≢ (trans (sym eq) (cong unres? (cong toℕ p)))
  unres-¬sep c eq (inj₂ (inj₁ p)) =
    bool≢ (trans (sym eq) (cong unres? (cong toℕ p)))
  unres-¬sep c eq (inj₂ (inj₂ (inj₁ p))) =
    bool≢ (trans (sym eq) (cong unres? (cong toℕ p)))
  unres-¬sep c eq (inj₂ (inj₂ (inj₂ p))) =
    bool≢ (trans (sym eq) (cong unres? (cong toℕ p)))

  -- на литеральных hex-цифрах всё редуцируется
  hex-safe : ∀ (k : Fin 16) → ¬ IsSep (toHex k)
  hex-safe F.zero = ¬sep≠ '0' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc F.zero) = ¬sep≠ '1' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc F.zero)) = ¬sep≠ '2' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc F.zero))) = ¬sep≠ '3' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc F.zero)))) = ¬sep≠ '4' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))) = ¬sep≠ '5' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))) = ¬sep≠ '6' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))) = ¬sep≠ '7' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))) = ¬sep≠ '8' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))) = ¬sep≠ '9' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))) = ¬sep≠ 'A' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))))) = ¬sep≠ 'B' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))))) = ¬sep≠ 'C' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))))))) = ¬sep≠ 'D' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))))))))))) = ¬sep≠ 'E' (λ ()) (λ ()) (λ ()) (λ ())
  hex-safe (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))))))))))) = ¬sep≠ 'F' (λ ()) (λ ()) (λ ()) (λ ())

  percent-safe : ¬ IsSep '%'
  percent-safe = ¬sep≠ '%' (λ ()) (λ ()) (λ ()) (λ ())

  encodeByteB-safe : ∀ (b : Byte) → Safe (encodeByteB b)
  encodeByteB-safe (b , b<256) =
    percent-safe ∷ hex-safe (fromℕ< q<16) ∷ hex-safe (fromℕ< r<16) ∷ []
    where
      q<16 : b / 16 < 16
      q<16 = m<n*o⇒m/o<n b<256
      r<16 : b % 16 < 16
      r<16 = m%n<n b 16

  safe-map : ∀ (f : Byte → List Char) → (∀ b → Safe (f b)) →
             ∀ bs → Safe² (map f bs)
  safe-map f pf []       = []
  safe-map f pf (b ∷ bs) = pf b ∷ safe-map f pf bs

  safe-++ : ∀ xs ys → Safe xs → Safe ys → Safe (xs ++ ys)
  safe-++ []       ys _     q = q
  safe-++ (x ∷ xs) ys (p ∷ px) q = p ∷ safe-++ xs ys px q

  safe-cat : ∀ xss → Safe² xss → Safe (cat xss)
  safe-cat []       []          = []
  safe-cat (xs ∷ xss) (p ∷ ps) = safe-++ xs (cat xss) p (safe-cat xss ps)

  bool-case : ∀ (b : Bool) {A : Set} → (b ≡ true → A) → (b ≡ false → A) → A
  bool-case true  f _ = f refl
  bool-case false _ g = g refl

  encChar-safe : ∀ c → toℕ c < 4194304 → Safe (encChar c)
  encChar-safe c p = bool-case (unres? (toℕ c)) (true-case c) (false-case c p)
    where
      true-case : ∀ c → unres? (toℕ c) ≡ true → Safe (encChar c)
      true-case c eq rewrite eq = unres-¬sep c eq ∷ []

      false-case : ∀ c → toℕ c < 4194304 → unres? (toℕ c) ≡ false → Safe (encChar c)
      false-case c p eq rewrite eq with toℕ c <? 65536
      ...   | yes q = safe-cat (map encodeByteB (utf8B (toℕ c) q))
                          (safe-map encodeByteB encodeByteB-safe (utf8B (toℕ c) q))
      ...   | no _ with toℕ c <? 4194304
      ...     | yes r = safe-cat (map encodeByteB (utf8B4 (toℕ c) r))
                            (safe-map encodeByteB encodeByteB-safe (utf8B4 (toℕ c) r))
      ...     | no nq = ⊥-elim (nq p)

  data WFList : List Char → Set where
    []  : WFList []
    _∷_ : ∀ c cs → toℕ c < 4194304 → WFList cs → WFList (c ∷ cs)

  go-safe : ∀ cs → WFList cs → Safe (go cs)
  go-safe [] [] = []
  go-safe (c ∷ cs) (_∷_ .c .cs p wf) =
    safe-++ (encChar c) (go cs) (encChar-safe c p) (go-safe cs wf)

-- ТС-safe: если все символы строки < 0x10000 (вся BMP: ASCII, кириллица, CJK),
-- закодированный вывод не содержит сырых ' ' '=' '&' '+'.
formEnc-safe : ∀ s → WFList (primStringToList s) → Safe (formEncList s)
formEnc-safe s wf = go-safe (primStringToList s) wf
