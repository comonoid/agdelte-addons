{-# OPTIONS --without-K #-}

-- СГЕНЕРИРОВАНО scripts/gen-form-vectors.mjs — НЕ править руками.
-- Источник: Stripe OpenAPI spec3 (openapi 3.0.0, info.version 2026-08-26.dahlia),
-- скачанный в spec/openapi.json (в git НЕ коммитится; см. скрипт — там curl).
-- Спека: POST /v1/checkout/sessions, requestBody
-- application/x-www-form-urlencoded (line_items[0][price_data][*], success_url,
-- metadata[k], client_reference_id, ...).
--
-- Каждый вектор: (имя, вход, ожидание); ожидание посчитано генератором по
-- RFC 3986 (неотэкранированы только A-Z a-z 0-9 - _ . ~; UTF-8, uppercase hex) —
-- те же правила, что у formEncS. Чеки (expected / mirror с Haskell / no-sep)
-- живут в agdelte/server/StripeTest.agda и именуются по вектору.
--
-- Замечания по расхождениям «спека ↔ клиент»:
-- * Спека требует percent-encoding значений (x-www-form-urlencoded); наш
--   энкодер соответствует RFC 3986 c uppercase hex — расхождений не найдено.
-- * Астральная плоскость (codepoints >= 0x10000) — известный баг энкодера
--   (3-байтовый UTF-8; см. шапку StripeForm.agda), в векторы сознательно
--   НЕ включён: зеркальные тесты эту зону не покрывают.
module Agdelte.Payment.StripeVectors where

open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

-- (имя, вход, ожидание)
Vector = String × String × String

vectors : List Vector
vectors =
    ( "success_url-url"
  , "https://example.com/success?sid=cs_123&x=1"
  , "https%3A%2F%2Fexample.com%2Fsuccess%3Fsid%3Dcs_123%26x%3D1" )
  ∷
  ( "success_url-ascii"
  , "cs_test_123-ok"
  , "cs_test_123-ok" )
  ∷
  ( "success_url-unicode"
  , "Путь в точку — 10 встреч"
  , "%D0%9F%D1%83%D1%82%D1%8C%20%D0%B2%20%D1%82%D0%BE%D1%87%D0%BA%D1%83%20%E2%80%94%2010%20%D0%B2%D1%81%D1%82%D1%80%D0%B5%D1%87" )
  ∷
  ( "success_url-cjk"
  , "中文キー"
  , "%E4%B8%AD%E6%96%87%E3%82%AD%E3%83%BC" )
  ∷
  ( "success_url-specials"
  , "a=b&c+d e%f~g"
  , "a%3Db%26c%2Bd%20e%25f~g" )
  ∷
  ( "success_url-long"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" )
  ∷
  ( "success_url-empty"
  , ""
  , "" )
  ∷
  ( "success_url-delims-only"
  , "&=+ %"
  , "%26%3D%2B%20%25" )
  ∷
  ( "cancel_url-url"
  , "https://example.com/cancel"
  , "https%3A%2F%2Fexample.com%2Fcancel" )
  ∷
  ( "cancel_url-ascii"
  , "cs_test_123-ok"
  , "cs_test_123-ok" )
  ∷
  ( "cancel_url-unicode"
  , "Путь в точку — 10 встреч"
  , "%D0%9F%D1%83%D1%82%D1%8C%20%D0%B2%20%D1%82%D0%BE%D1%87%D0%BA%D1%83%20%E2%80%94%2010%20%D0%B2%D1%81%D1%82%D1%80%D0%B5%D1%87" )
  ∷
  ( "cancel_url-cjk"
  , "中文キー"
  , "%E4%B8%AD%E6%96%87%E3%82%AD%E3%83%BC" )
  ∷
  ( "cancel_url-specials"
  , "a=b&c+d e%f~g"
  , "a%3Db%26c%2Bd%20e%25f~g" )
  ∷
  ( "cancel_url-long"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" )
  ∷
  ( "cancel_url-empty"
  , ""
  , "" )
  ∷
  ( "cancel_url-delims-only"
  , "&=+ %"
  , "%26%3D%2B%20%25" )
  ∷
  ( "client_reference_id-ascii"
  , "cs_test_123-ok"
  , "cs_test_123-ok" )
  ∷
  ( "client_reference_id-unicode"
  , "Путь в точку — 10 встреч"
  , "%D0%9F%D1%83%D1%82%D1%8C%20%D0%B2%20%D1%82%D0%BE%D1%87%D0%BA%D1%83%20%E2%80%94%2010%20%D0%B2%D1%81%D1%82%D1%80%D0%B5%D1%87" )
  ∷
  ( "client_reference_id-cjk"
  , "中文キー"
  , "%E4%B8%AD%E6%96%87%E3%82%AD%E3%83%BC" )
  ∷
  ( "client_reference_id-specials"
  , "a=b&c+d e%f~g"
  , "a%3Db%26c%2Bd%20e%25f~g" )
  ∷
  ( "client_reference_id-long"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" )
  ∷
  ( "client_reference_id-empty"
  , ""
  , "" )
  ∷
  ( "client_reference_id-delims-only"
  , "&=+ %"
  , "%26%3D%2B%20%25" )
  ∷
  ( "mode-payment"
  , "payment"
  , "payment" )
  ∷
  ( "mode-setup"
  , "setup"
  , "setup" )
  ∷
  ( "mode-subscription"
  , "subscription"
  , "subscription" )
  ∷
  ( "locale-auto"
  , "auto"
  , "auto" )
  ∷
  ( "locale-ru"
  , "ru"
  , "ru" )
  ∷
  ( "metadata-value-ascii"
  , "order-42"
  , "order-42" )
  ∷
  ( "metadata-value-unicode"
  , "заказ №42 — кириллица"
  , "%D0%B7%D0%B0%D0%BA%D0%B0%D0%B7%20%E2%84%9642%20%E2%80%94%20%D0%BA%D0%B8%D1%80%D0%B8%D0%BB%D0%BB%D0%B8%D1%86%D0%B0" )
  ∷
  ( "metadata-value-specials"
  , "k=v&k2+v 100%"
  , "k%3Dv%26k2%2Bv%20100%25" )
  ∷
  ( "metadata-value-long"
  , "mmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm"
  , "mmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmmm" )
  ∷
  ( "metadata-value-empty"
  , ""
  , "" )
  ∷
  ( "metadata-value-delims-only"
  , "=&+ "
  , "%3D%26%2B%20" )
  ∷
  ( "line_items-price_data-currency-eur"
  , "eur"
  , "eur" )
  ∷
  ( "line_items-price_data-currency-usd"
  , "usd"
  , "usd" )
  ∷
  ( "line_items-price_data-currency-bad-upper"
  , "EUR"
  , "EUR" )
  ∷
  ( "line_items-price_data-currency-empty"
  , ""
  , "" )
  ∷
  ( "line_items-price_data-unit_amount-one"
  , "1"
  , "1" )
  ∷
  ( "line_items-price_data-unit_amount-big"
  , "999999999"
  , "999999999" )
  ∷
  ( "line_items-price_data-unit_amount-zero"
  , "0"
  , "0" )
  ∷
  ( "line_items-quantity-one"
  , "1"
  , "1" )
  ∷
  ( "line_items-quantity-big"
  , "99999"
  , "99999" )
  ∷
  ( "line_items-quantity-zero"
  , "0"
  , "0" )
  ∷
  ( "line_items-product_data-name-ascii"
  , "cs_test_123-ok"
  , "cs_test_123-ok" )
  ∷
  ( "line_items-product_data-name-unicode"
  , "Путь в точку — 10 встреч"
  , "%D0%9F%D1%83%D1%82%D1%8C%20%D0%B2%20%D1%82%D0%BE%D1%87%D0%BA%D1%83%20%E2%80%94%2010%20%D0%B2%D1%81%D1%82%D1%80%D0%B5%D1%87" )
  ∷
  ( "line_items-product_data-name-cjk"
  , "中文キー"
  , "%E4%B8%AD%E6%96%87%E3%82%AD%E3%83%BC" )
  ∷
  ( "line_items-product_data-name-specials"
  , "a=b&c+d e%f~g"
  , "a%3Db%26c%2Bd%20e%25f~g" )
  ∷
  ( "line_items-product_data-name-long"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" )
  ∷
  ( "line_items-product_data-name-empty"
  , ""
  , "" )
  ∷
  ( "line_items-product_data-name-delims-only"
  , "&=+ %"
  , "%26%3D%2B%20%25" )
  ∷
  ( "line_items-product_data-description-ascii"
  , "cs_test_123-ok"
  , "cs_test_123-ok" )
  ∷
  ( "line_items-product_data-description-unicode"
  , "Путь в точку — 10 встреч"
  , "%D0%9F%D1%83%D1%82%D1%8C%20%D0%B2%20%D1%82%D0%BE%D1%87%D0%BA%D1%83%20%E2%80%94%2010%20%D0%B2%D1%81%D1%82%D1%80%D0%B5%D1%87" )
  ∷
  ( "line_items-product_data-description-cjk"
  , "中文キー"
  , "%E4%B8%AD%E6%96%87%E3%82%AD%E3%83%BC" )
  ∷
  ( "line_items-product_data-description-specials"
  , "a=b&c+d e%f~g"
  , "a%3Db%26c%2Bd%20e%25f~g" )
  ∷
  ( "line_items-product_data-description-long"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
  , "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" )
  ∷
  ( "line_items-product_data-description-empty"
  , ""
  , "" )
  ∷
  ( "line_items-product_data-description-delims-only"
  , "&=+ %"
  , "%26%3D%2B%20%25" )
  ∷
  ( "line_items-product_data-unit_label-ascii"
  , "cs_test_123-"
  , "cs_test_123-" )
  ∷
  ( "line_items-product_data-unit_label-unicode"
  , "Путь в точку"
  , "%D0%9F%D1%83%D1%82%D1%8C%20%D0%B2%20%D1%82%D0%BE%D1%87%D0%BA%D1%83" )
  ∷
  ( "line_items-product_data-unit_label-cjk"
  , "中文キー"
  , "%E4%B8%AD%E6%96%87%E3%82%AD%E3%83%BC" )
  ∷
  ( "line_items-product_data-unit_label-specials"
  , "a=b&c+d e%f~"
  , "a%3Db%26c%2Bd%20e%25f~" )
  ∷
  ( "line_items-product_data-unit_label-long"
  , "xxxxxxxxxxxx"
  , "xxxxxxxxxxxx" )
  ∷
  ( "line_items-product_data-unit_label-empty"
  , ""
  , "" )
  ∷
  ( "line_items-product_data-unit_label-delims-only"
  , "&=+ %"
  , "%26%3D%2B%20%25" )
  ∷ []
