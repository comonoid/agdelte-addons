{-# OPTIONS --without-K --guardedness #-}

-- Stripe REST client — domain-agnostic. GHC backend only. Structure mirrors
-- Agdelte.Payment.YooKassa: ONE import-first FOREIGN block, FFI on Haskell
-- tuples, ZERO new dependencies (http-client/http-client-tls/aeson and HMAC —
-- crypton — are already in the consumers' build-depends).
-- Depends only on the standard library (via Common for the shared HttpManager).
--
-- Primitives:
--   createCheckoutSession — POST /v1/checkout/sessions → CheckoutOk sessionId url
--   parseWebhookFields    — (event, object.id) from a webhook body (nested, injection-safe)
--   verifyWebhookSig      — Stripe-Signature check: HMAC-SHA256(secret, t <> "." <> body)
--                           vs ANY v1, freshness drift ≤ 300s (now passed in from outside)
--
-- No getSessionStatusRaw here (see the plan §2): no non-webhook consumer exists,
-- and dead code is worse than a missing primitive.
module Agdelte.Payment.Stripe where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; toList)
open import Agda.Builtin.String using (primStringToList)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Agda.Builtin.Char
  using (Char; primIsLower; primIsAscii)

open import Agdelte.Payment.Common
  using (HttpManager; _>>=_; pure)

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
  import Data.Aeson (Value(..), encode, decode)
  import qualified Data.Aeson.KeyMap as KM
  import qualified Data.Aeson.Key as K
  import Data.Maybe (mapMaybe)
  import Control.Exception (try, SomeException)
  import qualified Data.ByteString as BS
  import Data.Word (Word8)
  import Crypto.MAC.HMAC (HMAC, hmac, hmacGetDigest)
  import Crypto.Hash (SHA256)
  import qualified Data.ByteArray as BA

  type RawTripleH = (Integer, T.Text, T.Text)
  type RawPairH   = (T.Text, T.Text)

  -- application/x-www-form-urlencoded: UTF-8 байты значения, percent-encoding.
  -- (раньше было посимвольно по fromEnum — работало только для ASCII; на кириллице
  -- в description падало "index too large" и запрос молча умирал)
  formEnc :: T.Text -> String
  formEnc = concatMap ch . BS.unpack . TE.encodeUtf8
    where
      hex = "0123456789ABCDEF" :: String
      ch :: Word8 -> String
      ch w | (w >= 65 && w <= 90) || (w >= 97 && w <= 122)   -- A-Z a-z
             || (w >= 48 && w <= 57)                        -- 0-9
             || w == 45 || w == 95 || w == 46 || w == 126   -- - _ . ~
             = [toEnum (fromIntegral w)]
           | otherwise =
               ['%', hex !! (fromIntegral w `div` 16), hex !! (fromIntegral w `mod` 16)]

  formBody :: [(T.Text, T.Text)] -> String
  formBody fs = concat [ formEnc k ++ "=" ++ formEnc v ++ "&" | (k, v) <- fs ]

  -- POST /v1/checkout/sessions, Bearer + FORM-encoded body.
  -- (0, sessionId, hostedUrl) on success; (httpStatus, errText, "") on error.
  createCheckoutSessionRawHS :: HC.Manager -> T.Text -> T.Text -> T.Text -> T.Text
                             -> T.Text -> T.Text -> T.Text -> T.Text
                             -> T.Text -> T.Text
                             -> IO (Integer, T.Text, T.Text)
  createCheckoutSessionRawHS mgr account secretKey currency amountKop desc successUrl cancelUrl
                             clientRef metadata idemKey = do
    -- metadata: JSON object string → one-level metadata[k]=v form fields
    let metaPairs = case decode (LBS.fromStrict (TE.encodeUtf8 metadata)) :: Maybe Value of
          Just (Object o) ->
            [ ("metadata[" <> K.toText mk <> "]", case mv of String s -> s; _ -> T.empty)
            | (mk, mv) <- KM.toList o ]
          _ -> []
        fields =
          [ ("mode", "payment")
          , ("line_items[0][quantity]", "1")
          , ("line_items[0][price_data][currency]", T.toLower currency)
          , ("line_items[0][price_data][unit_amount]", amountKop)
          , ("line_items[0][price_data][product_data][name]", desc)
          , ("success_url", successUrl)
          , ("cancel_url", cancelUrl)
          , ("client_reference_id", clientRef)
          ] ++ metaPairs
        body = LBS.fromStrict (TE.encodeUtf8 (T.pack (formBody fields)))
        authHeader = "Bearer " <> TE.encodeUtf8 secretKey
        headers =
          [ ("Content-Type", "application/x-www-form-urlencoded")
          , ("Idempotency-Key", TE.encodeUtf8 idemKey)
          , ("Authorization", authHeader)
          ] ++ [ ("Stripe-Account", TE.encodeUtf8 account) | account /= T.empty ]
    -- базовый URL: STRIPE_API_BASE (тесты/эмулятор stripe-mock), дефолт — боевой API
    mbBase <- lookupEnv "STRIPE_API_BASE"
    let baseUrl = maybe "https://api.stripe.com" id mbBase
    initReq <- HC.parseRequest ("POST " ++ baseUrl ++ "/v1/checkout/sessions")
    let req = initReq
              { HC.requestBody = HC.RequestBodyLBS body
              , HC.requestHeaders = headers
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
                  mUrl = case KM.lookup (K.fromText "url") obj of
                    Just (String s) -> Just s
                    _               -> Nothing
              case (mId, mUrl) of
                (Just sid, Just curl) -> pure (0, sid, curl)
                _ -> pure (status, T.pack "Missing id or url in response", T.empty)
            _ -> pure (status, T.pack "Invalid JSON response", T.empty)
          else pure (status, TE.decodeUtf8 $ LBS.toStrict respBody, T.empty)

  -- (event, object.id) — nested lookup so a top-level "id" can't fool it.
  parseWebhookFieldsHS :: T.Text -> Maybe (T.Text, T.Text)
  parseWebhookFieldsHS body =
    case decode (LBS.fromStrict (TE.encodeUtf8 body)) :: Maybe Value of
      Just (Object o) -> do
        ev <- case KM.lookup (K.fromText "type") o of
                Just (String s) -> Just s
                _               -> Nothing
        obj <- case KM.lookup (K.fromText "data") o of
                Just (Object x) -> case KM.lookup (K.fromText "object") x of
                  Just (Object y) -> Just y
                  _               -> Nothing
                _               -> Nothing
        pid <- case KM.lookup (K.fromText "id") obj of
                Just (String s) -> Just s
                _               -> Nothing
        Just (ev, pid)
      _ -> Nothing

  -- Stripe-Signature: "t=...,v1=...,v1=..." — HMAC-SHA256(secret, t <> "." <> body)
  -- (secret as-is, whsec_...), constEq against ANY v1, freshness drift ≤ 300s.
  verifyWebhookSigHS :: T.Text -> T.Text -> T.Text -> T.Text -> Bool
  verifyWebhookSigHS now secret sigHeader body =
    let parts   = map (T.splitOn (T.pack "=")) (T.splitOn (T.pack ",") sigHeader)
                  ++ map (T.splitOn (T.pack "=")) (T.splitOn (T.pack " ") sigHeader)
        kvOf ps = case ps of [k, v] -> Just (T.strip k, T.strip v); _ -> Nothing
        kvs     = mapMaybe kvOf parts
        tVals   = [ v | (k, v) <- kvs, k == T.pack "t" ]
        v1s     = [ v | (k, v) <- kvs, k == T.pack "v1" ]
        nowN    = case reads (T.unpack now) :: [(Integer, String)] of
                    [(n, _)] -> n
                    _        -> 0
        fresh t = let tn = case reads (T.unpack t) :: [(Integer, String)] of
                             [(n, _)] -> n
                             _        -> nowN + 1000
                  in abs (nowN - tn) <= 300
        sigOk t = let expectedHex = T.pack $ show (hmacGetDigest
                        (hmac (TE.encodeUtf8 secret)
                              (TE.encodeUtf8 (T.concat [t, T.pack ".", body])) :: HMAC SHA256))
                    in or [ BA.constEq (TE.encodeUtf8 expectedHex) (TE.encodeUtf8 v1) | v1 <- v1s ]
    in case tVals of
         [t] -> fresh t && sigOk t
         _   -> False
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

-- | Result of a Stripe create-checkout-session call.
-- Инвариант в типе: CheckoutOk несёт ДОКАЗАТЕЛЬСТВО url ≢ "" — «тихий pending
-- с пустым confirmationUrl» (баг, найденный на stripe-mock-прогоне)
-- непредставим: сервер физически не может сконструировать такой результат.
data PaymentResult : Set where
  CheckoutOk    : (sid url : String) → ¬ (url ≡ "") → PaymentResult  -- sessionId, hosted url
  CheckoutError : ℕ → String → PaymentResult                         -- HTTP status (0 = network), error text

postulate
  createCheckoutSessionRaw : HttpManager → String → String → String → String → String → String
                           → String → String → String → String
                           → IO RawTriple
  -- (type, data.object.id) from a webhook body (raw FFI layer; the typed view is
  -- parseWebhookFields below)
  parseWebhookFieldsRaw : String → Maybe RawPair
  -- Stripe-Signature check; `now` (unix seconds) passed in from the caller
  verifyWebhookSig : String → String → String → String → Bool
{-# COMPILE GHC createCheckoutSessionRaw = createCheckoutSessionRawHS #-}
{-# COMPILE GHC parseWebhookFieldsRaw    = parseWebhookFieldsHS       #-}
{-# COMPILE GHC verifyWebhookSig         = verifyWebhookSigHS         #-}

------------------------------------------------------------------------
-- Типизированные валюта и сумма (Ур.1): невалидные конфиги непредставимы
------------------------------------------------------------------------

-- Валюта: НЕ-пустой СТРОЧНЫЙ ISO-код ("usd"/"eur"); умный конструктор
-- mkCurrency = парсер, верхний регистр/пустота отклоняются до сети.
data Currency : Set where
  isoCur : (code : String) → ¬ (code ≡ "") → Currency

curCode : Currency → String
curCode (isoCur c _) = c

-- все символы — строчные ASCII-латинские буквы (a-z)
lowerIsoᵇ : List Char → Bool
lowerIsoᵇ [] = true
lowerIsoᵇ (c ∷ cs) = (primIsAscii c ∧ primIsLower c) ∧ lowerIsoᵇ cs

mkCurrency : String → Maybe Currency
mkCurrency c with lowerIsoᵇ (primStringToList c) | c ≟ ""
... | true  | no ne = just (isoCur c ne)
... | _     | _     = nothing

-- Сумма: натуральная, > 0 (минорные единицы); ноль непредставим.
data Positive : Set where
  posNat : (n : ℕ) → ¬ (n ≡ zero) → Positive

amountOf : Positive → ℕ
amountOf (posNat n _) = n

mkPositive : ℕ → Maybe Positive
mkPositive zero    = nothing
mkPositive (suc n) = just (posNat (suc n) λ ())

------------------------------------------------------------------------
-- Ур.2: события вебхука как тип — диспетчер исчерпывающий по построению
------------------------------------------------------------------------

data StripeEvent : Set where
  SessionCompleted : (sid : String) → StripeEvent   -- checkout.session.completed, session id
  Unrecognized     : StripeEvent                    -- чужой/неизвестный type или непарсируемое тело

parseWebhookFields : String → StripeEvent
parseWebhookFields body with parseWebhookFieldsRaw body
... | nothing                          = Unrecognized
... | just pr with rpFst pr ≟ "checkout.session.completed"
...   | yes _ = SessionCompleted (rpSnd pr)
...   | no  _ = Unrecognized

-- | Create a Checkout Session. account ("" = no Stripe-Account header)/
-- secretKey/currency (типизированная: непустой строчный ISO-код — mkCurrency)/
-- amount (типизированная: натуральная > 0, минорные единицы — mkPositive)/
-- description/successUrl (absolute https, with {CHECKOUT_SESSION_ID})/cancelUrl/
-- clientRef/metadata-json/idempotencyKey → CheckoutOk | CheckoutError.
createCheckoutSession : HttpManager → String → String → Currency → Positive → String → String
                      → String → String → String → String
                      → IO PaymentResult
createCheckoutSession mgr account key cur amt desc success cancel cref meta idem =
  createCheckoutSessionRaw mgr account key (curCode cur)
    (natStr (amountOf amt)) desc success cancel cref meta idem >>= λ r →
  resolve (rtNat r) (rtFst r) (rtSnd r)
  where
    open import Data.Nat.Show using (show)
    natStr : ℕ → String
    natStr = show
    resolve : ℕ → String → String → IO PaymentResult
    -- успех: (0, sessionId, url); ошибка: (httpStatus|0, errText, "").
    -- 0 Double-books (успех и сетевой сбой Haskell-клиента), различаем по url:
    -- пустой url при status 0 = сетевая ошибка → CheckoutError (не маскировать!).
    -- Ветвление через Dec (а не Bool): в ветке `no ne` живёт доказательство
    -- url ≢ "", которое и требуется конструктору CheckoutOk.
    resolve zero    sid url with url ≟ ""
    ... | yes _ = pure (CheckoutError 0 sid)
    ... | no ne = pure (CheckoutOk sid url ne)
    resolve (suc n) err _   = pure (CheckoutError (suc n) err)
