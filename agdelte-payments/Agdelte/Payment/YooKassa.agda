{-# OPTIONS --without-K --guardedness #-}

-- ЮKassa (YooKassa) REST client — domain-agnostic. GHC backend only.
-- The OUTBOUND HTTP is this module's own http-client/TLS FFI (it calls
-- api.yookassa.ru), so it needs nothing from the framework's HTTP server.
-- Depends only on the standard library. A domain wires these primitives to its
-- own handlers/state.
--
-- Primitives:
--   newHttpManager       — TLS connection manager (create once at startup)
--   createPayment        — POST /v3/payments → PaymentOk paymentId confirmUrl
--   getPaymentStatusRaw  — GET /v3/payments/{id} → status re-fetch (available when a
--                          non-webhook consumer appears; unused API so far)
--   parseWebhookFieldsRaw — (event, object.id) raw FFI layer (nested, injection-safe)
--   parseWebhookFields   — typed YooKassaEvent (Ур.2): диспетчер исчерпывающий
--   verifyWebhookSig     — HMAC-SHA256 body check (defense-in-depth)
--
-- Типизированные входы (Ур.1): Currency — enum из OpenAPI-спеки ЮKassa
-- (components.schemas.CurrencyCode, spec/yookassa-openapi.yaml); Positive —
-- сумма > 0 в минорных единицах; форматирование "R.KK" — fmtAmount из
-- Agdelte.Payment.YooKassaForm (Agda строит тело, FFI берёт строку как есть).
--
-- Инвариант в типе: PaymentOk несёт ДОКАЗАТЕЛЬСТВО url ≢ «» — «тихий pending
-- с пустым confirmationUrl» непредставим (спека: ConfirmationRedirect
-- required [confirmation_url]; сеть/сервер всё равно могут вернуть пустой url
-- при status 0 — такие ответы классифицируются как PaymentError 0).
--
-- Базовый URL: YOOKASSA_API_BASE (тесты/эмулятор), дефолт — боевой API.
module Agdelte.Payment.YooKassa where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- IO plumbing (combinators + the ONE HttpManager type) comes from Common —
-- a second postulate of HttpManager here would be a nominally distinct
-- Agda type and PayConfig would not typecheck against Stripe functions.
open import Agdelte.Payment.Common
  using (HttpManager; newHttpManager; _>>=_; pure)

-- Типизированная сумма + форматтер "R.KK" (зеркало Haskell fmtKop);
-- ре-экспортируем, чтобы потребителям хватило одного импорта YooKassa.
open import Agdelte.Payment.YooKassaForm public
  using (Positive; posNat; mkPositive; amountOf; fmtAmount)

------------------------------------------------------------------------
-- All Haskell in ONE import-first FOREIGN block (MAlonzo strands the auto
-- `import Data.Text` after a block that ends in a definition).
------------------------------------------------------------------------

{-# FOREIGN GHC
  import qualified Network.HTTP.Client as HC
  import Network.HTTP.Types.Status (statusCode)
  import System.Environment (lookupEnv)
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

  type RawTripleH = (Integer, T.Text, T.Text)
  type RawPairH   = (T.Text, T.Text)

  -- Haskell-версия форматтера суммы (зеркало Agda fmtAmount из
  -- YooKassaForm). В боевом теле НЕ участвует (Агда строит сумму сама и
  -- передаёт готовую строку) — живёт для зеркальных векторов: независимая
  -- реализация, с которой сверяется Agda-версия.
  fmtKop :: T.Text -> T.Text
  fmtKop kop =
    let k = case reads (T.unpack kop) :: [(Integer, String)] of
              [(n, _)] -> max 0 n
              _        -> 0
        r = k `div` 100
        c = k `mod` 100
    in T.pack (show r ++ "." ++ (if c < 10 then "0" else "") ++ show c)

  -- POST /v3/payments. amount приходит УЖЕ отформатированным ("R.KK",
  -- Agda fmtAmount) — FFI не переформатывает, берёт как есть.
  -- (0, paymentId, confirmUrl) on success; (httpStatus, errText, "") on error.
  createPaymentRawHS :: HC.Manager -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text
                     -> IO (Integer, T.Text, T.Text)
  createPaymentRawHS mgr shopId secretKey currency amount desc returnUrl idemKey metadata = do
    let body = encode $ object
          [ "amount" .= object
              [ "value" .= amount
              , "currency" .= currency
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
    -- базовый URL: YOOKASSA_API_BASE (тесты/эмулятор), дефолт — боевой API
    mbBase <- lookupEnv "YOOKASSA_API_BASE"
    let baseUrl = maybe "https://api.yookassa.ru" id mbBase
    initReq <- HC.parseRequest ("POST " ++ baseUrl ++ "/v3/payments")
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
      mbBase <- lookupEnv "YOOKASSA_API_BASE"
      let baseUrl = maybe "https://api.yookassa.ru" id mbBase
      initReq <- HC.parseRequest (T.unpack (T.pack ("GET " ++ baseUrl ++ "/v3/payments/") <> paymentId))
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
  fmtKopHS  : String → String   -- Haskell-зеркало fmtAmount (только для тестов)
{-# COMPILE GHC RawTriple = type RawTripleH #-}
{-# COMPILE GHC rtNat = (\ t -> case t of (n,_,_) -> n :: Integer) #-}
{-# COMPILE GHC rtFst = (\ t -> case t of (_,a,_) -> a :: T.Text) #-}
{-# COMPILE GHC rtSnd = (\ t -> case t of (_,_,b) -> b :: T.Text) #-}
{-# COMPILE GHC RawPair = type RawPairH #-}
{-# COMPILE GHC rpFst = (fst :: RawPairH -> T.Text) #-}
{-# COMPILE GHC rpSnd = (snd :: RawPairH -> T.Text) #-}
{-# COMPILE GHC fmtKopHS = fmtKop #-}

------------------------------------------------------------------------
-- Клиент API
------------------------------------------------------------------------

-- | Result of a ЮKassa create-payment call.
-- Инвариант: PaymentOk несёт url ≢ "" (см. шапку модуля).
data PaymentResult : Set where
  PaymentOk    : (payId url : String) → ¬ (url ≡ "") → PaymentResult
  PaymentError : ℕ → String → PaymentResult         -- HTTP status (0 = network), error text

------------------------------------------------------------------------
-- Ур.1: валюта — enum из OpenAPI-спеки (components.schemas.CurrencyCode)
------------------------------------------------------------------------

data Currency : Set where
  rub : Currency
  eur : Currency
  usd : Currency
  kzt : Currency
  byn : Currency
  uah : Currency
  uzs : Currency
  try : Currency
  inr : Currency
  mdl : Currency
  azn : Currency
  amd : Currency

curCode : Currency → String
curCode rub = "RUB"
curCode eur = "EUR"
curCode usd = "USD"
curCode kzt = "KZT"
curCode byn = "BYN"
curCode uah = "UAH"
curCode uzs = "UZS"
curCode try = "TRY"
curCode inr = "INR"
curCode mdl = "MDL"
curCode azn = "AZN"
curCode amd = "AMD"

postulate
  createPaymentRaw : HttpManager → String → String → String → String → String → String → String → String
                   → IO RawTriple
  -- status fetch for non-webhook consumers (the webhook path itself trusts the
  -- SIGNED event after verifyWebhookSig — no re-fetch in webhookTx)
  getPaymentStatusRaw : HttpManager → String → String → String → IO RawTriple
  -- (event, object.id) from a webhook body (raw FFI layer; typed view below)
  parseWebhookFieldsRaw : String → Maybe RawPair
  -- HMAC-SHA256 body signature check
  verifyWebhookSig : String → String → String → Bool
{-# COMPILE GHC createPaymentRaw    = createPaymentRawHS    #-}
{-# COMPILE GHC getPaymentStatusRaw = getPaymentStatusRawHS #-}
{-# COMPILE GHC parseWebhookFieldsRaw = parseWebhookFieldsHS #-}
{-# COMPILE GHC verifyWebhookSig    = verifyWebhookSigHS    #-}

-- | Create a payment in ЮKassa. shopId/key/currency (enum из спеки)/amount
-- (типизированная: натуральная > 0, минорные единицы — mkPositive; форматти-
-- руется fmtAmount в "R.KK")/description/returnUrl/idempotencyKey/metadata-json
-- → PaymentOk | PaymentError.
createPayment : HttpManager → String → String → Currency → Positive → String → String
              → String → String
              → IO PaymentResult
createPayment mgr shopId key cur amt desc ret idem meta =
  createPaymentRaw mgr shopId key (curCode cur) (fmtAmount amt) desc ret idem meta >>= λ r →
  resolve (rtNat r) (rtFst r) (rtSnd r)
  where
    -- успех: (0, paymentId, url); ошибка: (httpStatus|0, errText, "").
    -- 0 Double-books (успех и сетевой сбой), различаем по url: пустой url при
    -- status 0 = сетевая ошибка → PaymentError (не маскировать!). Ветка `no ne`
    -- даёт доказательство url ≢ "", которое требует конструктор PaymentOk.
    resolve : ℕ → String → String → IO PaymentResult
    resolve zero    payId url with url ≟ ""
    ... | yes _ = pure (PaymentError 0 payId)
    ... | no ne = pure (PaymentOk payId url ne)
    resolve (suc n) err _   = pure (PaymentError (suc n) err)

------------------------------------------------------------------------
-- Ур.2: события вебхука как тип — диспетчер исчерпывающий по построению
------------------------------------------------------------------------

data YooKassaEvent : Set where
  PaymentSucceeded : (pid : String) → YooKassaEvent   -- payment.succeeded, payment id
  PaymentCanceled  : (pid : String) → YooKassaEvent   -- payment.canceled, payment id
  Unrecognized     : YooKassaEvent                    -- чужой event или непарсируемое тело

parseWebhookFields : String → YooKassaEvent
parseWebhookFields body with parseWebhookFieldsRaw body
... | nothing = Unrecognized
... | just pr with rpFst pr ≟ "payment.succeeded"
...   | yes _ = PaymentSucceeded (rpSnd pr)
...   | no _ with rpFst pr ≟ "payment.canceled"
...     | yes _ = PaymentCanceled (rpSnd pr)
...     | no _  = Unrecognized
