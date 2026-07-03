# agdelte-store

A small **domain-agnostic embedded store** for Agda (GHC backend), extracted from
the agdelte project. Depends only on the standard library.

- `Agdelte.Storage.NatMap` — `Data.Map`-backed map keyed by ℕ (postulate).
- `Agdelte.Storage.IndexedMap` — a NatMap with declared, auto-maintained secondary
  indexes (abstract; index invariant holds by construction).
- `Agdelte.Storage.Wire` — pure length-prefix codec primitives + a reader monad.
- `Agdelte.Storage.WAL` — write-ahead log: `walTxn` (transaction-atomic, durable-
  before-visible via `modifyMVarMasked`), byte-framed + CRC32 recovery.
- `Agdelte.Storage.Txn` — a generic transaction monad parameterized over your
  `(S, Op, E, apply)`; `emit op = apply + log`, difference-list accumulator,
  `runTxn` yields exactly what `walTxn` consumes (live ≡ replay by construction).
- `Agdelte.Storage.FFI` — self-contained GHC FFI (MVar/modifyMVarMasked + durable
  WAL file ops); no dependency on the agdelte framework.

A domain provides its records, an `Op` sum type, `apply : Op → S → S`, and a wire
codec, and gets an indexed, transactional, crash-recoverable in-memory store.

## Install
Register in `~/.agda/libraries`:
```
/path/to/agdelte-store/agdelte-store.agda-lib
```
then `depend: agdelte-store` in your `.agda-lib`.
