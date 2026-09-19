#!/usr/bin/env node
// Генератор тест-векторов форматтера суммы ЮKassa (уровень 4 корректности,
// зеркало gen-form-vectors.mjs страйповского энкодера).
//
// Читает машиночитаемую OpenAPI-спеку ЮKassa и строит векторы
// (имя, вход-копейки, ожидание "R.KK") для fmtAmount / fmtKop:
// суммы всех «интересных» сортов — одна копейка, круглые, «хвостатый ноль»,
// крупная; ожидание считает сам генератор НЕЗАВИСИМОЙ реализацией правил
// MonetaryAmount.value из спеки (dot separator, ровно две цифры после точки).
//
// Спека: https://yookassa.ru/developers/api/yookassa-openapi-specification.yaml
// (OpenAPI 3.0.2). В git НЕ коммитится; регенерация:
//   curl -sL -o spec/yookassa-openapi.yaml \
//     https://yookassa.ru/developers/api/yookassa-openapi-specification.yaml
//   node scripts/gen-yookassa-vectors.mjs
//
// Из спеки скрипту нужны только (а) CurrencyCode enum — сверяется с enum'ом
// Currency в YooKassa.agda; (б) описание MonetaryAmount.value — фиксируется в
// шапке сгенерированного модуля. Полный YAML-парсер не нужен: эти два блока
// вырезаются регуляркой по стабильному machine-generated стилю спеки;
// любое отклонение = ошибка генерации, а не тихий пропуск.
//
// Дополнительно (пин страйповского типа, зеркальные векторы): ожидание
// сверяется и с Agda-версией (fmtAmount), и с Haskell-версией (fmtKop) в
// agdelte/server/YooKassaTest.agda — по три чека на вектор
// (expected / mirror / no-raw-json).

import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const specPath = join(root, "spec", "yookassa-openapi.yaml");
const outPath = join(root, "Agdelte", "Payment", "YooKassaVectors.agda");

const spec = readFileSync(specPath, "utf8");

// ---------------------------------------------------------------- спека
// MonetaryAmount.value: описание контракта "R.KK"
const amountBlock = spec.match(
  /    MonetaryAmount:\n      description: [^\n]*\n      type: "object"\n      properties:\n        value:\n          description: "([^"]+)"/,
);
if (!amountBlock) {
  console.error("spec: не найден components.schemas.MonetaryAmount.value.description");
  process.exit(1);
}
const valueDescription = amountBlock[1];
if (!/fractional form/.test(valueDescription) || !/dot/.test(valueDescription)) {
  console.error("spec: неожиданный контракт MonetaryAmount.value:\n  " + valueDescription);
  process.exit(1);
}

// CurrencyCode enum (сверка с Agda-enum'ом Currency — расхождение = ошибка)
const curBlock = spec.match(/CurrencyCode:\n(?:.*\n)*?      enum:\n((?:      - "\w+"\n)+)/);
if (!curBlock) {
  console.error("spec: не найден components.schemas.CurrencyCode.enum");
  process.exit(1);
}
const specCurrencies = [...curBlock[1].matchAll(/- "(\w+)"/g)].map((m) => m[1]);

// enum из Agdelte.Payment.YooKassa (curCode) — единственный источник истины
// для кодов; спека должна его ПОКРЫВАТЬ.
const agdaSource = readFileSync(join(root, "Agdelte", "Payment", "YooKassa.agda"), "utf8");
const agdaCurrencies = [...agdaSource.matchAll(/^curCode [^ ]+ = "([A-Z]+)"/gm)].map(
  (m) => m[1],
);
if (agdaCurrencies.length === 0) {
  console.error("yookassa.agda: не найден curCode (enum Currency)");
  process.exit(1);
}
const missing = agdaCurrencies.filter((c) => !specCurrencies.includes(c));
if (missing.length > 0) {
  console.error(
    `спека/клиент разошлись: кодов нет в спеке: ${missing.join(", ")}` +
      `\n  спека: ${specCurrencies.join(" ")}`,
  );
  process.exit(1);
}

// ------------------------------------------------- независимая реализация R.KK
// Правила MonetaryAmount.value: «always in fractional form, the separator for
// the fractional part is a dot, no separator is used for thousands» — для
// двухзнаковых валют: копейки → рубли с ровно двумя цифрами после точки.
function fmtKop(kopecks) {
  if (!Number.isInteger(kopecks) || kopecks < 1) throw new Error("kopecks must be positive");
  const rub = Math.floor(kopecks / 100);
  const kop = String(kopecks % 100);
  return String(rub) + "." + (kop.length < 2 ? "0" + kop : kop);
}

// ---------------------------------------------------------------- построение
const vectors = []; // { name, input (копейки, десятичная строка), expected }

function add(name, kopecks) {
  vectors.push({ name, input: String(kopecks), expected: fmtKop(kopecks) });
}

// минимальные/однозначные
add("min", 1);                         // 0.01 — ведущий ноль в дробной части
add("nine", 9);                        // 0.09
add("ten", 10);                        // 0.10 — хвостовой ноль
add("eleven", 11);                     // 0.11
add("max-kop-no-pad", 99);             // 0.99
// переход через рубль
add("one-rub", 100);                   // 1.00
add("one-rub-one", 101);               // 1.01
add("one-rub-ten", 110);               // 1.10
add("almost-two", 199);                // 1.99
add("two-rub", 200);                   // 2.00
add("leading-zero-rubs", 999);         // 9.99 (целая часть одной цифрой)
// круглые и «широкие»
add("round-10", 1000);                 // 10.00
add("real", 12345);                    // 123.45
add("round-1000", 100000);             // 1000.00 — без разделителей тысяч
add("round-100k", 10000000);           // 100000.00
add("big", 99999999999);               // 999999999.99
add("big-plus-one", 100000000001);     // 1000000000.01

// ---------------------------------------------------------------- Agda-вывод
function agdaString(s) {
  return '"' + s.replace(/\\/g, "\\\\").replace(/"/g, '\\"') + '"';
}

// версия спеки/заголовок
const specTitle = (spec.match(/^  title: "([^"]+)"/m) ?? [, "unknown"])[1];
const specVersion = (spec.match(/^  version: "([^"]+)"/m) ?? [, "unknown"])[1];

const header = `{-# OPTIONS --without-K #-}

-- СГЕНЕРИРОВАНО scripts/gen-yookassa-vectors.mjs — НЕ править руками.
-- Источник: ЮKassa OpenAPI specification (${specTitle}, openapi 3.0.2,
-- info.version ${specVersion}), скачанный в spec/yookassa-openapi.yaml
-- (в git НЕ коммитится; см. скрипт — там curl).
-- Контракт MonetaryAmount.value из спеки: «${valueDescription}»
-- (для RUB — ровно две цифры после точки).
--
-- Каждый вектор: (имя, вход-копейки, ожидание "R.KK"); ожидание посчитано
-- генератором НЕЗАВИСИМОЙ реализацией правил спеки. Чеки (expected / mirror
-- Agda fmtAmount vs Haskell fmtKop / no-raw-json) живут в
-- agdelte/server/YooKassaTest.agda и именуются по вектору.
--
-- Сверка «спека ↔ клиент»: CurrencyCode enum спеки покрывает весь enum
-- Currency в YooKassa.agda (${agdaCurrencies.join(" ")}) — расхождений не найдено.
module Agdelte.Payment.YooKassaVectors where

open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

-- (имя, вход-копейки, ожидание)
Vector = String × String × String
`;

const body =
  vectors
    .map(
      (v) =>
        `    ( ${agdaString(v.name)}\n  , ${agdaString(v.input)}\n  , ${agdaString(v.expected)} )`,
    )
    .join("\n  ∷\n") + "\n  ∷ []";

const moduleText = `${header}

vectors : List Vector
vectors =
${body}
`;

writeFileSync(outPath, moduleText);
console.log(
  `OK: ${vectors.length} векторов → ${outPath}` +
    ` (spec ${specVersion}, валют в спеке: ${specCurrencies.length})`,
);
