{-# OPTIONS --without-K #-}

-- СГЕНЕРИРОВАНО scripts/gen-yookassa-vectors.mjs — НЕ править руками.
-- Источник: ЮKassa OpenAPI specification (YooMoney API Reference, openapi 3.0.2,
-- info.version 1.0.0), скачанный в spec/yookassa-openapi.yaml
-- (в git НЕ коммитится; см. скрипт — там curl).
-- Контракт MonetaryAmount.value из спеки: «Amount in the selected currency, always in fractional form. The separator for the fractional part is a dot, no separator is used for thousands. The number of digits after the dot depends on the selected currency. Example: 1000.00.»
-- (для RUB — ровно две цифры после точки).
--
-- Каждый вектор: (имя, вход-копейки, ожидание "R.KK"); ожидание посчитано
-- генератором НЕЗАВИСИМОЙ реализацией правил спеки. Чеки (expected / mirror
-- Agda fmtAmount vs Haskell fmtKop / no-raw-json) живут в
-- agdelte/server/YooKassaTest.agda и именуются по вектору.
--
-- Сверка «спека ↔ клиент»: CurrencyCode enum спеки покрывает весь enum
-- Currency в YooKassa.agda (RUB EUR USD KZT BYN UAH UZS TRY INR MDL AZN AMD) — расхождений не найдено.
module Agdelte.Payment.YooKassaVectors where

open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

-- (имя, вход-копейки, ожидание)
Vector = String × String × String


vectors : List Vector
vectors =
    ( "min"
  , "1"
  , "0.01" )
  ∷
    ( "nine"
  , "9"
  , "0.09" )
  ∷
    ( "ten"
  , "10"
  , "0.10" )
  ∷
    ( "eleven"
  , "11"
  , "0.11" )
  ∷
    ( "max-kop-no-pad"
  , "99"
  , "0.99" )
  ∷
    ( "one-rub"
  , "100"
  , "1.00" )
  ∷
    ( "one-rub-one"
  , "101"
  , "1.01" )
  ∷
    ( "one-rub-ten"
  , "110"
  , "1.10" )
  ∷
    ( "almost-two"
  , "199"
  , "1.99" )
  ∷
    ( "two-rub"
  , "200"
  , "2.00" )
  ∷
    ( "leading-zero-rubs"
  , "999"
  , "9.99" )
  ∷
    ( "round-10"
  , "1000"
  , "10.00" )
  ∷
    ( "real"
  , "12345"
  , "123.45" )
  ∷
    ( "round-1000"
  , "100000"
  , "1000.00" )
  ∷
    ( "round-100k"
  , "10000000"
  , "100000.00" )
  ∷
    ( "big"
  , "99999999999"
  , "999999999.99" )
  ∷
    ( "big-plus-one"
  , "100000000001"
  , "1000000000.01" )
  ∷ []
