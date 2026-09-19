{-# OPTIONS --without-K --guardedness #-}

-- Common payment-client plumbing shared by every provider module (YooKassa,
-- Stripe, …). GHC backend only. The HttpManager type MUST live in exactly one
-- place: two identical postulates would be nominally distinct Agda types, and
-- a PayConfig built with one would not typecheck against the other provider's
-- functions. Own IO combinators keep the library independent of the framework
-- FFI (deliberate duplication of Agdelte.FFI.Server). Depends only on the
-- standard library.
module Agdelte.Payment.Common where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- All Haskell in ONE import-first FOREIGN block (MAlonzo strands the auto
-- `import Data.Text` after a block that ends in a definition).
------------------------------------------------------------------------

{-# FOREIGN GHC
  import qualified Network.HTTP.Client as HC
  import qualified Network.HTTP.Client.TLS as TLS

  type HttpManagerT = HC.Manager

  -- Явные таймауты: провайдерский HTTP-вызов не должен висеть вечно (дефолт
  -- defaultManagerSettings = 30s «тихо», здесь — явные 15s и keep-alive 60s).
  newHttpManagerHS :: IO HC.Manager
  newHttpManagerHS = HC.newManager settings
    where
      -- TLS.tlsManagerSettings :: HC.ManagerSettings (http-client-tls) с ЯВНЫМ
      -- responseTimeout 15s (дефолт менеджера «тихий», провайдерский вызов
      -- не должен висеть вечно)
      settings = TLS.tlsManagerSettings
        { HC.managerResponseTimeout = HC.responseTimeoutMicro 15000000 }
  #-}

------------------------------------------------------------------------
-- Connection manager + IO combinators
------------------------------------------------------------------------

postulate
  HttpManager    : Set
  newHttpManager : IO HttpManager
  _>>=_ : ∀ {A B : Set} → IO A → (A → IO B) → IO B
  pure  : ∀ {A : Set} → A → IO A
{-# COMPILE GHC HttpManager    = type HttpManagerT #-}
{-# COMPILE GHC newHttpManager = newHttpManagerHS  #-}
{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC pure  = \_ -> return #-}
infixl 1 _>>=_
