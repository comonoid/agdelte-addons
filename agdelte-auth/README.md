# agdelte-auth

Generic security library, extracted from the agdelte framework. Domain-neutral; sits
above the framework and is consumed by domain libs.

- `Agdelte.Auth.JWT` — JWT sign/verify (HS256 via `FFI.Crypto.hmacSHA256`).
- `Agdelte.Auth.SignedUrl` — HMAC-signed, expiring URLs (gated downloads etc.).
- `Agdelte.Auth.Role` — role/permission checks.
- `Agdelte.Auth.Middleware` — HTTP bearer/auth middleware over `FFI.Server`.
- `Agdelte.Auth.Client` — auth client (`Core.Cmd` HTTP).

Depends DOWN only: `standard-library`, `agdelte` (framework: FFI.Crypto/Server/Time/Json,
Core.Cmd). The framework core imports zero auth. Module names kept `Agdelte.Auth.*` so
consumers' imports are unchanged.
