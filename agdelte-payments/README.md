# agdelte-payments

Payment-provider clients for Agda (GHC backend), domain-agnostic. Depends only on
the standard library.

- `Agdelte.Payment.YooKassa` — the ЮKassa (YooKassa) REST client: `createPayment`
  (POST /v3/payments → confirmation URL), `getPaymentStatusRaw` (status re-fetch
  for non-webhook consumers; the webhook path itself trusts the SIGNED event),
  `parseWebhookFieldsRaw` (nested, injection-safe), `verifyWebhookSig` (HMAC-SHA256
  defense-in-depth). Outbound HTTP is the module's own `http-client`/TLS FFI — no
  framework HTTP server needed. Base URL overridable via `YOOKASSA_API_BASE` env
  (default `https://api.yookassa.ru` — for test rigs).
  Typed layer (mirrors Stripe's): `Currency` is an enum straight from the
  OpenAPI spec (`components.schemas.CurrencyCode`); amounts are `Positive`
  (minor units, zero unrepresentable); `PaymentOk` carries a PROOF
  `url ≢ ""`; `parseWebhookFields` returns a typed `YooKassaEvent`
  (`PaymentSucceeded` / `PaymentCanceled` / `Unrecognized`) so the server
  dispatcher is exhaustive by construction. **Currency reachability**: the
  chosen `Currency` is passed to the FFI and sent in the body (a regression
  where the body hardcoded RUB is pinned by the mock smoke, see
  `agdelte` `test:yk-mock`).
  Theorems (Ур.3): `fmt-safe` — the formatted amount NEVER contains raw `"` or
  `\` (JSON-safe for ALL inputs, no hypotheses); `fmt-roundtrip` —
  `parseAmount (fmtList p) ≡ amountOf p` (format → parse is the identity).
- `Agdelte.Payment.YooKassaForm` — Agda mirror of the Haskell `fmtKop` amount
  formatter (kopecks → `"R.KK"`, contract from the spec's
  `MonetaryAmount.value`). Level-3 invariant: the output NEVER contains raw
  `"` or `\` (JSON-safe by construction — digits via literal `Fin 10` cases,
  whole part by well-founded recursion). Spec-derived amount vectors live in
  `YooKassaVectors`; generator: `scripts/gen-yookassa-vectors.mjs` reads the
  YooKassa OpenAPI spec (`spec/yookassa-openapi.yaml`, NOT committed,
  https://yookassa.ru/developers/api/yookassa-openapi-specification.yaml) and
  cross-checks the `CurrencyCode` enum against the client.
- `Agdelte.Payment.Stripe` — the Stripe Checkout client (base URL overridable
  via `STRIPE_API_BASE` env, default `https://api.stripe.com` — for stripe-mock
  and test rigs): `createCheckoutSession`
  (POST /v1/checkout/sessions, form-encoded body, `Idempotency-Key`, optional
  `Stripe-Account` header), `parseWebhookFields` (`(type, data.object.id)`,
  nested, injection-safe), `verifyWebhookSig` (`Stripe-Signature`:
  HMAC-SHA256(secret, `t <> "." <> body`) vs ANY v1, 300s freshness with `now`
  passed in from the caller).
- `Agdelte.Payment.StripeForm` — Agda-side mirror of the Stripe form encoder
  (`formEncS`, UTF-8 → percent-encoding); mirror vectors in `stripe-test` pin
  it to the Haskell encoder. `PaymentResult` carries a typed invariant:
  `CheckoutOk` requires a proof `url ≢ "` (an empty confirmationUrl is
  unrepresentable). Spec-derived form vectors: `scripts/gen-form-vectors.mjs`
  reads the Stripe OpenAPI spec (`spec/openapi.json`, NOT committed) and
  generates `Agdelte.Payment.StripeVectors` (71 vectors × 3 checks:
  expected / mirror vs Haskell / no-sep; ВКЛЮЧАЯ астральные пробы-эмодзи —
  пин фикса 4-байтового UTF-8) — the spec-vs-client conformance
  layer of the form encoder. `scripts/check-stripe-vectors.sh` regenerates
  and requires byte-equality (spec-drift alarm); `agdelte` `test:stripe-mock`
  runs a network smoke against the vendored stripe-mock binary.
- `Agdelte.Payment.Common` — shared plumbing: THE `HttpManager` postulate
  (`type HC.Manager` / `newHttpManager`) and its own IO combinators. The manager
  type must be postulated exactly once (two identical postulates would be
  nominally distinct Agda types and a config built with one would not typecheck
  against the other provider's functions); provider modules import it from here.

Room for a future provider-neutral interface in the same library. A domain wires
these primitives to its own handlers/state.

## Webhook signature model (ЮKassa vs Stripe)

ЮKassa does NOT sign its webhook notifications — there is no official
HMAC over the body (unlike Stripe's `Stripe-Signature`). The official
protection mechanism is an **IP allowlist** of ЮKassa notification senders,
configured on the receiving side. Therefore:

- `verifyWebhookSig` for YooKassa is **defense-in-depth by agreement**: the
  domain (e.g. cxm-pack-psych) sends its own HMAC in `x-yookassa-signature`
  when the webhook passes through its own proxy/infrastructure, and the
  client verifies it. It protects the proxy path, not against ЮKassa itself.
- The real perimeter against third parties must be the IP allowlist on the
  HTTP-server/proxy layer — client code cannot provide it.
- Stripe, by contrast, is genuinely signed (`t=…,v1=…`, freshness 300s), and
  `Agdelte.Payment.Stripe.verifyWebhookSig` implements the official scheme.

Do not mistake the YooKassa `verifyWebhookSig` for an official-provider check:
without the allowlist, an attacker posting a valid-looking body (with the
HMAC, if the proxy key leaks) would pass.

## Install
Register in `~/.agda/libraries`:
```
/path/to/agdelte-payments/agdelte-payments.agda-lib
```
then `depend: agdelte-payments`. The FFI needs (when GHC-built): http-client,
http-client-tls, http-types, aeson, bytestring, base64-bytestring, crypton,
memory, text.
