{-# OPTIONS --without-K --guardedness #-}

-- The Postgres-side interpreter of the freer Tx (pg-store-plan Ф1): one reified program →
-- one PG transaction on ONE pinned connection. The domain supplies an `Exec` — how to run a
-- single verb over a live connection (compile to SQL via Storage.SQL/Query, run via
-- execConn/queryConn, decode via Storage.JsonRow) — and this module owns the transaction
-- semantics, identical for every TxRunner (connect-per-txn / own pool / pgbouncer):
--
--   BEGIN → fold the program verb-by-verb (read-your-own-writes: uncommitted writes are
--   visible to this txn's own SELECTs — PG gives it for free) → COMMIT on ret / ROLLBACK on
--   fail or on a verb-level error (e.g. a lock-discipline rejection).
--
-- READ COMMITTED by design (pg-store-plan «Конкурентность») — no SET TRANSACTION here; the
-- lock discipline (lockRoot verbs → FOR UPDATE / pg_advisory_xact_lock) carries correctness.
-- Typechecks against the PgConn contract now; runs once the driver session fills the pragmas.
module Agdelte.Storage.FreeIO (Req : Set) (Ans : Req → Set) (E : Set) where

open import Agda.Builtin.IO using (IO)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Agdelte.Storage.Free Req Ans E using (Tx; ret; fail; call)
open import Agdelte.Storage.PgConn using (Conn; execConn; TxRunner; withConn)
open import Agdelte.Storage.FFI using (_>>=_; pure)

-- run ONE verb on the open transaction's connection; inj₁ aborts the whole transaction
Exec : Set
Exec = Conn → (r : Req) → IO (E ⊎ Ans r)

private
  -- fold the program inside the open transaction (total: `k x` is a constructor-field call)
  step : Conn → Exec → ∀ {A} → Tx A → IO (E ⊎ A)
  step c exec (ret a)    = pure (inj₂ a)
  step c exec (fail e)   = pure (inj₁ e)
  step c exec (call r k) = exec c r >>= go
    where go : _ → IO _
          go (inj₁ e) = pure (inj₁ e)
          go (inj₂ x) = step c exec (k x)

-- the whole transaction: BEGIN … COMMIT/ROLLBACK on one pinned connection
runTxPg : TxRunner → Exec → ∀ {A} → Tx A → IO (E ⊎ A)
runTxPg run exec tx = withConn run λ c →
  execConn c "BEGIN;" >>= λ _ →
  step c exec tx >>= finish c
  where
    finish : Conn → ∀ {A} → E ⊎ A → IO (E ⊎ A)
    finish c (inj₁ e) = execConn c "ROLLBACK;" >>= λ _ → pure (inj₁ e)
    finish c (inj₂ a) = execConn c "COMMIT;"   >>= λ _ → pure (inj₂ a)