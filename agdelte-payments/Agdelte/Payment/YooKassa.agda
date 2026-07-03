{-# OPTIONS --without-K --guardedness #-}

-- ЮKassa (YooKassa) REST client — domain-agnostic. GHC backend only.
-- The OUTBOUND HTTP is this module's own http-client/TLS FFI (it calls
-- api.yookassa.ru), so it needs nothing from the framework's HTTP server.
-- Depends only on the standard library. A domain wires these primitives to its
-- own handlers/state.
--
-- Primitives:
--   newHttpManager       — TLS connection manager (create once at startup)
--   createPayment        — POST /v3/payments → PaymentOk paymentId confirmUrl | PaymentError
--   getPaymentStatusRaw  — GET /v3/payments/{id} → authoritative status (never trust the webhook body)
--   parseWebhookFields   — (event, object.id) from a webhook body (nested, injection-safe)
--   verifyWebhookSig     — HMAC-SHA256 body check (defense-in-depth; status re-fetch is authoritative)
module Agdelte.Payment.YooKassa where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)

-- own IO combinators — keep the client independent of the framework FFI
postulate
  _>>=_ : ∀ {A B : Set} → IO A → (A → IO B) → IO B
  pure  : ∀ {A : Set} → A → IO A
{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC pure  = \_ -> return #-}
infixl 1 _>>=_

------------------------------------------------------------------------
-- All Haskell in ONE import-first FOREIGN block (MAlonzo strands the auto
-- `import Data.Text` after a block that ends in a definition).
------------------------------------------------------------------------

{-# FOREIGN GHC
  import qualified Network.HTTP.Client as HC
  import qualified Network.HTTP.Client.TLS as TLS
  import Network.HTTP.Types.Status (statusCode)
  import qualified Data.Text as T
  import qualified Data.Text.Encoding as TE
  import qualified Data.ByteString.Lazy as LBS
  import qualified Data.ByteString.Base64 as B64
  import Data.Aeson (Value(..), object, (.=), encode, decode)
  import qualified Data.Aeson.KeyMap as KM
  import qualified Data.Aeson.Key as K
  import Control.Exception (try, SomeException)
  import Crypto.MAC.HMAC (HMAC, hmac, hmacGetDigest)
  import Crypto.Hash (SHA256)
  import qualified Data.ByteArray as BA

  type HttpManagerT = HC.Manager
  type RawTripleH = (Integer, T.Text, T.Text)
  type RawPairH   = (T.Text, T.Text)

  newHttpManagerHS :: IO HC.Manager
  newHttpManagerHS = TLS.newTlsManager

  -- POST /v3/payments. (0, paymentId, confirmUrl) on success; (httpStatus, errText, "") on error.
  createPaymentRawHS :: HC.Manager -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text
                     -> IO (Integer, T.Text, T.Text)
  createPaymentRawHS mgr shopId secretKey amount desc returnUrl idemKey metadata = do
    let amountRub = case reads (T.unpack amount) :: [(Integer, String)] of
          [(k, _)] -> let r = k `div` 100
                          kop = k `mod` 100
                      in T.pack $ show r ++ "." ++ (if kop < 10 then "0" else "") ++ show kop
          _        -> "0.00"
        body = encode $ object
          [ "amount" .= object
              [ "value" .= amountRub
              , "currency" .= ("RUB" :: T.Text)
              ]
          , "confirmation" .= object
              [ "type" .= ("redirect" :: T.Text)
              , "return_url" .= returnUrl
              ]
          , "capture" .= True
          , "description" .= desc
          , "metadata" .= case decode (LBS.fromStrict $ TE.encodeUtf8 metadata) of
              Just v  -> (v :: Value)
              Nothing -> object []
          ]
        authHeader = "Basic " <> B64.encode (TE.encodeUtf8 shopId <> ":" <> TE.encodeUtf8 secretKey)
    initReq <- HC.parseRequest "POST https://api.yookassa.ru/v3/payments"
    let req = initReq
              { HC.requestBody = HC.RequestBodyLBS body
              , HC.requestHeaders =
                  [ ("Content-Type", "application/json")
                  , ("Idempotency-Key", TE.encodeUtf8 idemKey)
                  , ("Authorization", authHeader)
                  ]
              }
    result <- try (HC.httpLbs req mgr) :: IO (Either SomeException (HC.Response LBS.ByteString))
    case result of
      Left ex -> pure (0, T.pack $ "Network error: " ++ show ex, T.empty)
      Right resp -> do
        let status = fromIntegral (statusCode (HC.responseStatus resp)) :: Integer
            respBody = HC.responseBody resp
        if status >= 200 && status < 300
          then case decode respBody :: Maybe Value of
            Just (Object obj) -> do
              let mId = case KM.lookup (K.fromText "id") obj of
                    Just (String s) -> Just s
                    _               -> Nothing
                  mUrl = case KM.lookup (K.fromText "confirmation") obj of
                    Just (Object conf) -> case KM.lookup (K.fromText "confirmation_url") conf of
                      Just (String s) -> Just s
                      _               -> Nothing
                    _ -> Nothing
              case (mId, mUrl) of
                (Just pid, Just curl) -> pure (0, pid, curl)
                _ -> pure (status, T.pack "Missing id or confirmation_url in response", T.empty)
            _ -> pure (status, T.pack "Invalid JSON response", T.empty)
          else pure (status, TE.decodeUtf8 $ LBS.toStrict respBody, T.empty)

  -- GET /v3/payments/{id} → authoritative status. (0, status, "") | (httpStatus, errText, "").
  getPaymentStatusRawHS :: HC.Manager -> T.Text -> T.Text -> T.Text
                        -> IO (Integer, T.Text, T.Text)
  getPaymentStatusRawHS mgr shopId secretKey paymentId = do
    let authHeader = "Basic " <> B64.encode (TE.encodeUtf8 shopId <> ":" <> TE.encodeUtf8 secretKey)
    result <- try (do
      initReq <- HC.parseRequest (T.unpack ("GET https://api.yookassa.ru/v3/payments/" <> paymentId))
      let req = initReq { HC.requestHeaders = [ ("Authorization", authHeader) ] }
      HC.httpLbs req mgr) :: IO (Either SomeException (HC.Response LBS.ByteString))
    case result of
      Left ex -> pure (0, T.pack ("Network error: " ++ show ex), T.empty)
      Right resp -> do
        let status = fromIntegral (statusCode (HC.responseStatus resp)) :: Integer
            respBody = HC.responseBody resp
        if status >= 200 && status < 300
          then case decode respBody :: Maybe Value of
            Just (Object obj) -> case KM.lookup (K.fromText "status") obj of
              Just (String s) -> pure (0, s, T.empty)
              _               -> pure (status, T.pack "Missing status in payment", T.empty)
            _ -> pure (status, T.pack "Invalid JSON response", T.empty)
          else pure (status, TE.decodeUtf8 $ LBS.toStrict respBody, T.empty)

  -- (event, object.id) — nested lookup so a top-level "id" can't fool it.
  parseWebhookFieldsHS :: T.Text -> Maybe (T.Text, T.Text)
  parseWebhookFieldsHS body =
    case decode (LBS.fromStrict (TE.encodeUtf8 body)) :: Maybe Value of
      Just (Object o) -> do
        ev <- case KM.lookup (K.fromText "event") o of
                Just (String s) -> Just s
                _               -> Nothing
        obj <- case KM.lookup (K.fromText "object") o of
                Just (Object x) -> Just x
                _               -> Nothing
        pid <- case KM.lookup (K.fromText "id") obj of
                Just (String s) -> Just s
                _               -> Nothing
        Just (ev, pid)
      _ -> Nothing

  -- HMAC-SHA256(secret, body) compared to the signature header (defense-in-depth).
  verifyWebhookSigHS :: T.Text -> T.Text -> T.Text -> Bool
  verifyWebhookSigHS secret sigHeader body =
    let expected = T.pack $ show (hmacGetDigest
          (hmac (TE.encodeUtf8 secret) (TE.encodeUtf8 body) :: HMAC SHA256))
    in BA.constEq (TE.encodeUtf8 expected) (TE.encodeUtf8 sigHeader)
  #-}

------------------------------------------------------------------------
-- Connection manager
------------------------------------------------------------------------

postulate
  HttpManager    : Set
  newHttpManager : IO HttpManager
{-# COMPILE GHC HttpManager    = type HttpManagerT #-}
{-# COMPILE GHC newHttpManager = newHttpManagerHS  #-}

------------------------------------------------------------------------
-- FFI boundary tuples (Agda's Σ can't cross a COMPILE GHC type → Haskell tuples)
------------------------------------------------------------------------

postulate
  RawTriple : Set
  rtNat     : RawTriple → ℕ
  rtFst     : RawTriple → String
  rtSnd     : RawTriple → String
  RawPair   : Set
  rpFst     : RawPair → String
  rpSnd     : RawPair → String
{-# COMPILE GHC RawTriple = type RawTripleH #-}
{-# COMPILE GHC rtNat = (\ t -> case t of (n,_,_) -> n :: Integer) #-}
{-# COMPILE GHC rtFst = (\ t -> case t of (_,a,_) -> a :: T.Text) #-}
{-# COMPILE GHC rtSnd = (\ t -> case t of (_,_,b) -> b :: T.Text) #-}
{-# COMPILE GHC RawPair = type RawPairH #-}
{-# COMPILE GHC rpFst = (fst :: RawPairH -> T.Text) #-}
{-# COMPILE GHC rpSnd = (snd :: RawPairH -> T.Text) #-}

------------------------------------------------------------------------
-- Client API
------------------------------------------------------------------------

-- | Result of a ЮKassa create-payment call.
data PaymentResult : Set where
  PaymentOk    : String → String → PaymentResult  -- paymentId, confirmationUrl
  PaymentError : ℕ → String → PaymentResult         -- HTTP status (0 = network), error text

postulate
  createPaymentRaw : HttpManager → String → String → String → String → String → String → String
                   → IO RawTriple
  -- authoritative status fetch (source of truth; the webhook body is NOT trusted)
  getPaymentStatusRaw : HttpManager → String → String → String → IO RawTriple
  -- (event, object.id) from a webhook body
  parseWebhookFields : String → Maybe RawPair
  -- HMAC-SHA256 body signature check
  verifyWebhookSig : String → String → String → Bool
{-# COMPILE GHC createPaymentRaw    = createPaymentRawHS    #-}
{-# COMPILE GHC getPaymentStatusRaw = getPaymentStatusRawHS #-}
{-# COMPILE GHC parseWebhookFields  = parseWebhookFieldsHS  #-}
{-# COMPILE GHC verifyWebhookSig    = verifyWebhookSigHS    #-}

-- | Create a payment in ЮKassa. shopId/key/amount(kopecks as decimal string)/
-- description/returnUrl/idempotencyKey/metadata-json → PaymentOk | PaymentError.
createPayment : HttpManager → String → String → String → String → String → String → String
              → IO PaymentResult
createPayment mgr shopId key amt desc ret idem meta =
  createPaymentRaw mgr shopId key amt desc ret idem meta >>= λ r →
  resolve (rtNat r) (rtFst r) (rtSnd r)
  where
    open import Data.Nat using (zero; suc)
    resolve : ℕ → String → String → IO PaymentResult
    resolve zero    payId url = pure (PaymentOk payId url)
    resolve (suc n) err   _   = pure (PaymentError (suc n) err)
