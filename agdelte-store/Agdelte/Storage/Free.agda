{-# OPTIONS --without-K --safe #-}

-- Freer transaction monad over an abstract verb signature — the Tx core of the PG-only plan (Ф1).
-- A command is a REIFIED program: `call r k` names a store verb `r` and continues with its answer.
-- One program, many interpreters:
--   * `runTx` (here): pure, over an explicit state — the REFERENCE semantics. Doubles as the
--     lock-discipline checker (a handler may reject a verb, aborting the txn) and as the test
--     backend: commands are tested without any database.
--   * the Postgres interpreter (later, in IO over the driver): one BEGIN … COMMIT/ROLLBACK,
--     verbs become SELECT/UPSERT/DELETE/FOR-UPDATE statements.
--
-- Totality: NO sized types, NO TERMINATING pragma. The continuation is a constructor FIELD, so
-- `k x` is structurally smaller — the same principle that lets W-types recurse. `--safe` holds.
--
-- Instantiation: a domain supplies `Req` (its verb GADT), `Ans` (each verb's answer type) and `E`
-- (its abort/error type):  `open import Agdelte.Storage.Free Req Ans E`.
module Agdelte.Storage.Free
  (Req : Set) (Ans : Req → Set) (E : Set) where

open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- The reified transaction
------------------------------------------------------------------------

data Tx (A : Set) : Set where
  ret  : A → Tx A                            -- pure result
  fail : E → Tx A                            -- abort the whole transaction
  call : (r : Req) → (Ans r → Tx A) → Tx A   -- perform a verb, continue with its answer

------------------------------------------------------------------------
-- Monad ops — all total, no pragmas
------------------------------------------------------------------------

returnT : ∀ {A} → A → Tx A
returnT = ret

infixl 1 _>>=T_ _>>T_

_>>=T_ : ∀ {A B} → Tx A → (A → Tx B) → Tx B
ret a    >>=T f = f a
fail e   >>=T f = fail e
call r k >>=T f = call r (λ x → k x >>=T f)

_>>T_ : ∀ {A B} → Tx A → Tx B → Tx B
m >>T n = m >>=T λ _ → n

abortT : ∀ {A} → E → Tx A
abortT = fail

-- perform one verb
opT : (r : Req) → Tx (Ans r)
opT r = call r ret

guardT : Bool → E → Tx ⊤
guardT true  _ = ret tt
guardT false e = fail e

------------------------------------------------------------------------
-- Native interpreter — the reference semantics (pure, stateful, abortable)
------------------------------------------------------------------------

-- A handler runs one verb over the state; it may REJECT it (inj₁), aborting the transaction —
-- that is where the lock-discipline checker lives (e.g. a write without its root lock held).
Handler : Set → Set
Handler S = (r : Req) → S → E ⊎ (Ans r × S)

runTx : ∀ {S A} → Handler S → Tx A → S → E ⊎ (A × S)
runTx h (ret a)    s = inj₂ (a , s)
runTx h (fail e)   s = inj₁ e
runTx h (call r k) s with h r s
... | inj₁ e        = inj₁ e
... | inj₂ (x , s′) = runTx h (k x) s′
