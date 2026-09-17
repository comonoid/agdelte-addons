# agdelte-payments

Payment-provider clients for Agda (GHC backend), domain-agnostic. Depends only on
the standard library.

- `Agdelte.Payment.YooKassa` — the ЮKassa (YooKassa) REST client: `createPayment`
  (POST /v3/payments → confirmation URL), `getPaymentStatusRaw` (status re-fetch
  for non-webhook consumers; the webhook path itself trusts the SIGNED event),
  `parseWebhookFields` (nested, injection-safe), `verifyWebhookSig` (HMAC-SHA256
  defense-in-depth). Outbound HTTP is the module's own `http-client`/TLS FFI — no
  framework HTTP server needed.
- `Agdelte.Payment.Stripe` — the Stripe Checkout client: `createCheckoutSession`
  (POST /v1/checkout/sessions, form-encoded body, `Idempotency-Key`, optional
  `Stripe-Account` header), `parseWebhookFields` (`(type, data.object.id)`,
  nested, injection-safe), `verifyWebhookSig` (`Stripe-Signature`:
  HMAC-SHA256(secret, `t <> "." <> body`) vs ANY v1, 300s freshness with `now`
  passed in from the caller).
- `Agdelte.Payment.Common` — shared plumbing: THE `HttpManager` postulate
  (`type HC.Manager` / `newHttpManager`) and its own IO combinators. The manager
  type must be postulated exactly once (two identical postulates would be
  nominally distinct Agda types and a config built with one would not typecheck
  against the other provider's functions); provider modules import it from here.

Room for a future provider-neutral interface in the same library. A domain wires
these primitives to its own handlers/state.

## Install
Register in `~/.agda/libraries`:
```
/path/to/agdelte-payments/agdelte-payments.agda-lib
```
then `depend: agdelte-payments`. The FFI needs (when GHC-built): http-client,
http-client-tls, http-types, aeson, bytestring, base64-bytestring, crypton,
memory, text.
