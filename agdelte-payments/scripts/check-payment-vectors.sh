#!/usr/bin/env bash
# Чек конформанс «векторы ↔ генератор ↔ спека»: регенерирует
# Agdelte/Payment.YooKassaVectors и требует байт-в-байт совпадения с
# закоммиченным. Расхождение = спека обновилась или генератор поехал.
# (Спека spec/yookassa-openapi.yaml в git НЕ коммитится; если её нет —
# скрипт сам скачивает актуальную. См. шапку gen-yookassa-vectors.mjs.)
set -euo pipefail
cd "$(dirname "$0")/.."

SPEC=spec/yookassa-openapi.yaml
if [ ! -f "$SPEC" ]; then
  mkdir -p spec
  curl -sL -o "$SPEC" \
    https://yookassa.ru/developers/api/yookassa-openapi-specification.yaml
fi

node scripts/gen-yookassa-vectors.mjs >/dev/null
if ! git diff --exit-code --quiet Agdelte/Payment/YooKassaVectors.agda; then
  echo "✗ YooKassaVectors.agda разошёлся с генератором/спекой — регенерируй и закоммить:"
  echo "    node scripts/gen-yookassa-vectors.mjs"
  git --no-pager diff -- Agdelte/Payment/YooKassaVectors.agda | head -30
  exit 1
fi
echo "✓ векторы в синхроне с генератором и спекой"
