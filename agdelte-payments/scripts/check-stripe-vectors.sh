#!/usr/bin/env bash
# Чек конформанс «векторы ↔ генератор ↔ спека» для Stripe: регенерирует
# Agdelte/Payment.StripeVectors и требует байт-в-байт совпадения с
# закоммиченным. Спека spec/openapi.json в git НЕ коммитится; если её нет —
# скрипт сам скачивает актуальную (см. шапку gen-form-vectors.mjs).
set -euo pipefail
cd "$(dirname "$0")/.."

SPEC=spec/openapi.json
if [ ! -f "$SPEC" ]; then
  mkdir -p spec
  curl -sL -o "$SPEC" \
    https://raw.githubusercontent.com/stripe/openapi/master/openapi/spec3.json
fi

node scripts/gen-form-vectors.mjs >/dev/null
if ! git diff --exit-code --quiet Agdelte/Payment/StripeVectors.agda; then
  echo "✗ StripeVectors.agda разошёлся с генератором/спекой — регенерируй и закоммить:"
  echo "    node scripts/gen-form-vectors.mjs"
  git --no-pager diff -- Agdelte/Payment/StripeVectors.agda | head -30
  exit 1
fi
echo "✓ векторы в синхроне с генератором и спекой"
