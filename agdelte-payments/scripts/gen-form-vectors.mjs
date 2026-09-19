#!/usr/bin/env node
// Генератор тест-векторов form-энкодера (уровень 4 корректности Stripe).
//
// Читает машиночитаемую OpenAPI-спеку Stripe и строит векторы
// (имя, вход, ожидание) для formEncS / formEnc: значения полей
// POST /v1/checkout/sessions (line_items[0][price_data][*], success_url,
// metadata[k], client_reference_id, ...) всех «интересных» сортов:
// ascii, unicode (BMP), спецсимволы = & + % и длинные строки; плюс
// граничные (пустая строка, только разделители).
//
// Ожидание считает сам генератор по RFC 3986: неотэкранированы только
// A-Z a-z 0-9 - _ . ~ ; всё остальное → %XX (UTF-8, ЗАГЛАВНЫЕ hex) —
// в точности правила Agdelte.Payment.StripeForm.formEncS.
//
// Спека НЕ коммитится в git; путь и версия зафиксированы в шапке
// сгенерированного модуля. Регенерация:
//   curl -sL -o spec/openapi.json https://raw.githubusercontent.com/stripe/openapi/master/openapi/spec3.json
//   node scripts/gen-form-vectors.mjs
//
// Астральная плоскость (эмодзи): энкодер починен на честный 4-байтовый
// UTF-8 (см. шапку StripeForm.agda), поэтому астральные пробы ВКЛЮЧЕНЫ
// в векторы наравне с остальными и пинят фикс зеркалом с Haskell.

import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const specPath = join(root, "spec", "openapi.json");
const outPath = join(root, "Agdelte", "Payment", "StripeVectors.agda");

const spec = JSON.parse(readFileSync(specPath, "utf8"));
const specVersion = spec?.info?.version ?? "unknown";

const op =
  spec.paths["/v1/checkout/sessions"]?.post?.requestBody?.content[
    "application/x-www-form-urlencoded"
  ]?.schema;
if (!op || !op.properties) {
  console.error("spec: нет form-схемы POST /v1/checkout/sessions");
  process.exit(1);
}
const props = op.properties;

// ---------------------------------------------------------------- RFC 3986
const UNRESERVED = new Set(
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_.~",
);

function rfc3986Encode(str) {
  const bytes = Buffer.from(str, "utf8");
  let out = "";
  for (const b of bytes) {
    const c = String.fromCharCode(b);
    out += UNRESERVED.has(c) ? c : "%" + b.toString(16).toUpperCase().padStart(2, "0");
  }
  return out;
}

// ------------------------------------------------------------- построение
const vectors = []; // { name, input, expected }

function add(name, input) {
  vectors.push({ name, input, expected: rfc3986Encode(input) });
}

// набор значений-проб для строкового поля; maxLen — из спеки (maxLength)
function probeField(key, valueSet, maxLen) {
  for (const [tag, v] of valueSet) {
    const val = maxLen && v.length > maxLen ? v.slice(0, maxLen) : v;
    add(`${key}-${tag}`, val);
  }
}

const standardProbes = [
  ["ascii", "cs_test_123-ok"],
  ["emoji", "оплата 💳 曲🎉"],
  ["unicode", "Путь в точку — 10 встреч"],
  ["cjk", "中文キー"],
  ["specials", "a=b&c+d e%f~g"],           // ~ остаётся сырым (RFC 3986 unreserved)
  ["long", "x".repeat(512)],
  ["empty", ""],
  ["delims-only", "&=+ %"],
];

// строковые поля верхнего уровня (maxLength, если задан, берём из спеки)
for (const [key, extra] of [
  ["success_url", [["url", "https://example.com/success?sid=cs_123&x=1"]]],
  ["cancel_url", [["url", "https://example.com/cancel"]]],
  ["client_reference_id", []],
  ["mode", [["payment", "payment"], ["setup", "setup"], ["subscription", "subscription"]]],
  ["locale", [["auto", "auto"], ["ru", "ru"]]],
]) {
  const sch = props[key];
  if (!sch) continue;
  const probes = [...extra, ...standardProbes];
  // enum-поля не имеют смысла для пустой/разделительной пробы
  const filtered = sch.enum ? probes.filter(([, v]) => sch.enum.includes(v)) : probes;
  probeField(key, filtered, sch.maxLength);
}

// metadata[k]: additionalProperties: { type: string }
if (props.metadata?.additionalProperties) {
  for (const [tag, v] of [
    ["ascii", "order-42"],
    ["unicode", "заказ №42 — кириллица"],
    ["specials", "k=v&k2+v 100%"],
    ["long", "m".repeat(500)],
    ["empty", ""],
    ["delims-only", "=&+ "],
  ]) {
    add(`metadata-value-${tag}`, v);
  }
}

// line_items[0][price_data][*]
const li = props.line_items?.items?.properties;
if (li) {
  const pd = li.price_data?.properties;
  if (pd?.currency)
    probeField("line_items-price_data-currency", [
      ["eur", "eur"], ["usd", "usd"], ["bad-upper", "EUR"], ["empty", ""],
    ]);
  if (pd?.unit_amount)
    probeField("line_items-price_data-unit_amount", [
      ["one", "1"], ["big", "999999999"], ["zero", "0"],
    ]);
  if (li.quantity)
    probeField("line_items-quantity", [["one", "1"], ["big", "99999"], ["zero", "0"]]);
  const prod = pd?.product_data?.properties;
  if (prod) {
    for (const key of ["name", "description", "unit_label"]) {
      if (!prod[key]) continue;
      probeField(`line_items-product_data-${key}`, standardProbes, prod[key].maxLength);
    }
  }
}

// ------------------------------------------------------------- Agda-вывод
function agdaString(s) {
  return '"' + s.replace(/\\/g, "\\\\").replace(/"/g, '\\"') + '"';
}

const header = `{-# OPTIONS --without-K #-}

-- СГЕНЕРИРОВАНО scripts/gen-form-vectors.mjs — НЕ править руками.
-- Источник: Stripe OpenAPI spec3 (openapi 3.0.0, info.version ${specVersion}),
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
`;

const body =
  vectors
    .map(
      (v) =>
        `  ( ${agdaString(v.name)}\n  , ${agdaString(v.input)}\n  , ${agdaString(v.expected)} )`,
    )
    .join("\n  ∷\n") + "\n  ∷ []";

const moduleText = `${header}
vectors : List Vector
vectors =
  ${body}
`;

writeFileSync(outPath, moduleText);
console.log(
  `OK: ${vectors.length} векторов → ${outPath} (spec ${specVersion})`,
);
