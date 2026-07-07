{-# OPTIONS --without-K #-}

-- Conn-centric FFI contract (pg-store-plan.md «Драйвер», 2026-07-05) — the AGDA HALF only:
-- these postulates FIX the signatures; the Haskell implementations + COMPILE GHC pragmas land
-- in the driver session (agdelte-store/hs/Agdelte/Postgres.hs). Everything above this seam
-- builds on the four primitives + two derived capabilities and may NEVER mention Pool/conninfo:
--
--   primitives: connect / close / execConn / queryConn
--   derived:    withConnRaw (bracket) → TxRunner       — транзакционный мир (v1 connect-per-txn,
--               v2 свой пул, pgbouncer — меняется ТОЛЬКО раннер, ничего выше шва)
--               long-lived SessionConn                  — сессионный мир (LISTEN / session-prepared /
--               cross-txn temp), владелец — именованный компонент, 1-2 на процесс
--
-- Scope discipline (pg-store-plan): внутри раннера — ТОЛЬКО txn-scoped фичи
-- (pg_advisory_xact_lock, SET LOCAL, ON COMMIT DROP, RETURNING). Сессионное — только на
-- выделенных SessionConn. BEGIN/COMMIT/ROLLBACK/FOR UPDATE — обычные строки через execConn.
module Agdelte.Storage.PgConn where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

postulate
  Conn : Set                              -- opaque physical connection

  -- open/close one physical connection (libpq conninfo / postgresql:// URI).
  -- Direct use is for SessionConn owners (connect and keep + reconnect on drop);
  -- transactional code goes through withConnRaw/TxRunner instead.
  connect : String → IO Conn
  close   : Conn → IO ⊤

  -- run ONE statement on THIS connection. Multi-statement transactions are sequences of
  -- these between BEGIN and COMMIT/ROLLBACK on the same Conn.
  execConn  : Conn → String → IO Nat      -- INSERT/UPDATE/DELETE/DDL → affected rows
  queryConn : Conn → String → IO String   -- SELECT → JSON array (same shape as Postgres.queryJson)

  -- scoped acquisition: MUST be a Haskell `bracket connect close` — close is guaranteed on ANY
  -- exception; exception-safety lives HERE (Agda cannot catch). Explicit ROLLBACK on domain
  -- aborts is the Tx interpreter's job; the bracket is the last-resort safety net.
  withConnRaw : ∀ {A : Set} → String → (Conn → IO A) → IO A

------------------------------------------------------------------------
-- TxRunner — the transactional-world capability (the swappable piece)
------------------------------------------------------------------------

-- NB: a plain polymorphic function, NOT a record — MAlonzo compiles a rank-2 record field into
-- a newtype with existential type variables, which GHC rejects. The `withConn` accessor is kept
-- so call sites read the same; v2's pooledRunner is just another value of this type.
TxRunner : Set₁
TxRunner = ∀ {A : Set} → (Conn → IO A) → IO A

withConn : TxRunner → ∀ {A : Set} → (Conn → IO A) → IO A
withConn r = r

-- v1: a fresh connection per transaction (~1-2ms; pgbouncer in front makes this cheap with
-- zero code changes). v2 (own pool) adds `pooledRunner : Pool → TxRunner` with the same field —
-- the interpreter and all Tx programs are untouched. NB v2-пул обязан санировать возврат
-- (ROLLBACK/discard упавших в транзакции соединений).
connectPerTxn : String → TxRunner
connectPerTxn conninfo k = withConnRaw conninfo k

------------------------------------------------------------------------
-- Reserved, NOT postulated yet (adds additively when needed):
--   awaitNotification : Conn → IO String   -- LISTEN/NOTIFY wakeups on a dedicated SessionConn
-- Pending the hpgsql async-notification capability check (driver session). Near-term nothing
-- needs LISTEN: single-process worker wakes via an in-process post-commit nudge, the rest polls.
-- Its real slot is multi-process: a split-out worker and WS-push fan-out across web replicas.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- V1 IMPLEMENTATION (2026-07-07): connection-per-transaction over the EXISTING pool driver —
-- a PRIVATE one-connection pool per transaction IS a connection (nobody else holds its handle,
-- so statements cannot interleave; concurrent transactions get their own connections → real
-- concurrency, no global lock). ~1-2ms connect overhead per txn — the accepted v1 cost;
-- pgbouncer in front makes it cheap with zero code changes.
--
-- V2 (пользовательская драйверная сессия: много транзакций на долгоживущем коннекте):
--   * заменить ТЕЛА этих прагм настоящим Conn-API (true connect/close);
--   * ДОБАВИТЬ `pooledRunner : Pool → TxRunner` рядом с connectPerTxn (аддитивно; выше шва
--     ничего не меняется — команды/Exec/runCxmTx зависят только от TxRunner);
--   * пул ОБЯЗАН санировать возвраты: соединение, вернувшееся посреди транзакции (исключение
--     Haskell сбежало из блока), ROLLBACK'ается или выбрасывается — грязным не выдаётся.
------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Agdelte.Postgres as PG #-}
{-# FOREIGN GHC import qualified Control.Exception as CEx #-}
{-# FOREIGN GHC import qualified Data.IORef as CRef #-}
{-# FOREIGN GHC import qualified System.IO.Unsafe as CUnsafe #-}
{-# FOREIGN GHC
-- round-trip counter (audit A6 chattiness): every exec/query bumps it; the bench reads+resets.
pgStmtCtr :: CRef.IORef Integer
pgStmtCtr = CUnsafe.unsafePerformIO (CRef.newIORef 0)
{-# NOINLINE pgStmtCtr #-}
pgBump :: IO ()
pgBump = CRef.modifyIORef' pgStmtCtr (+1)
#-}
{-# COMPILE GHC Conn = type PG.Pool #-}
{-# COMPILE GHC connect = \s -> PG.newPool s 1 #-}
{-# COMPILE GHC close = PG.closePool #-}
{-# COMPILE GHC execConn = \c s -> pgBump >> PG.execSql c s #-}
{-# COMPILE GHC queryConn = \c s -> pgBump >> PG.queryJson c s #-}
{-# COMPILE GHC withConnRaw = \_ s k -> CEx.bracket (PG.newPool s 1) PG.closePool k #-}

-- round-trip instrumentation (A6): statements since the last reset, and a reset.
postulate
  pgStmtCount : IO Nat
  pgStmtReset : IO ⊤
{-# COMPILE GHC pgStmtCount = CRef.readIORef pgStmtCtr #-}
{-# COMPILE GHC pgStmtReset = CRef.writeIORef pgStmtCtr 0 #-}
