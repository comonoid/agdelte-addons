# agdelte-payments

Payment-provider clients for Agda (GHC backend), domain-agnostic. Depends only on
the standard library.

- `Agdelte.Payment.YooKassa` — the ЮKassa (YooKassa) REST client: `createPayment`
  (POST /v3/payments → confirmation URL), `getPaymentStatusRaw` (authoritative
  status re-fetch — the webhook body is never trusted), `parseWebhookFields`
  (nested, injection-safe), `verifyWebhookSig` (HMAC-SHA256 defense-in-depth).
  Outbound HTTP is the module's own `http-client`/TLS FFI — no framework HTTP
  server needed.

Room for `Agdelte.Payment.Stripe` and a future provider-neutral interface in the
same library. A domain wires these primitives to its own handlers/state.

## Install
Register in `~/.agda/libraries`:
```
/path/to/agdelte-payments/agdelte-payments.agda-lib
```
then `depend: agdelte-payments`. The FFI needs (when GHC-built): http-client,
http-client-tls, http-types, aeson, bytestring, base64-bytestring, cryptonite,
memory, text.
