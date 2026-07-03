{-# OPTIONS --without-K --guardedness #-}

-- Self-contained FFI for the embedded store (GHC/MAlonzo only). Carved from the
-- agdelte framework's FFI.Server + FFI.FileSystem so this library depends ONLY on
-- the standard library: IO combinators, MVar + modifyMVarMasked (the exception-safe
-- read-modify-write the WAL commits under), and the durable byte-framed WAL file
-- operations (append+fsync, CRC-checked record reader).
--
-- All Haskell lives in ONE import-first FOREIGN block: MAlonzo appends its own
-- `import Data.Text` after user FOREIGN blocks, so a block ending in a definition
-- strands that import → GHC parse error. Imports first, definitions after.

module Agdelte.Storage.FFI where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Data.Maybe using (Maybe)

{-# FOREIGN GHC
  import qualified Data.Text as T
  import qualified Data.Text.IO as TIO
  import qualified Control.Exception as Ex
  import qualified Control.Concurrent.MVar as MVar
  import qualified Data.ByteString as BS
  import qualified Data.ByteString.Char8 as BC
  import Data.Text.Encoding (encodeUtf8, decodeUtf8With)
  import Data.Text.Encoding.Error (lenientDecode)
  import System.IO (withFile, withBinaryFile, hFlush, IOMode(WriteMode, AppendMode))
  import System.Directory (doesFileExist)
  import qualified System.FilePath as FP
  import System.Posix.IO (handleToFd, closeFd, openFd, OpenMode(ReadOnly), defaultFileFlags)
  import System.Posix.Unistd (fileSynchronise)
  import Control.Monad (when)
  import Data.Word (Word8, Word32)
  import Data.Bits (xor, shiftR, (.&.))
  import Data.List (foldl')

  tryCatchImpl :: IO a -> IO (Maybe a)
  tryCatchImpl act = fmap eitherToMaybe (Ex.try act)
    where eitherToMaybe :: Either Ex.SomeException b -> Maybe b
          eitherToMaybe (Right a) = Just a
          eitherToMaybe (Left _)  = Nothing

  -- fsync the directory CONTAINING the path, so a create/rename in it survives
  -- power loss (a file fsync persists data+inode, not the directory entry).
  syncPathDirHS :: T.Text -> IO ()
  syncPathDirHS path = do
    let raw = FP.takeDirectory (T.unpack path)
        dir = if null raw then "." else raw
    r <- Ex.try (do
      fd <- openFd dir ReadOnly defaultFileFlags
      fileSynchronise fd
      closeFd fd) :: IO (Either Ex.SomeException ())
    either (const (return ())) return r

  -- Durable write: write → flush → fsync before returning.
  durableWriteHS :: IOMode -> T.Text -> T.Text -> IO ()
  durableWriteHS mode path content =
    withFile (T.unpack path) mode $ \h -> do
      TIO.hPutStr h content
      hFlush h
      fd <- handleToFd h
      fileSynchronise fd
      closeFd fd

  -- pure CRC32 (poly 0xEDB88320), bit-by-bit (no table/dep); fine at recovery time.
  walCrcStep :: Word32 -> Word8 -> Word32
  walCrcStep crc byte = go (8 :: Int) (crc `xor` fromIntegral byte)
    where go 0 c = c
          go k c = go (k - 1) (if c .&. 1 /= 0 then (c `shiftR` 1) `xor` 0xEDB88320 else c `shiftR` 1)
  walCrc32 :: BS.ByteString -> Word32
  walCrc32 bs = 0xFFFFFFFF `xor` BS.foldl' walCrcStep 0xFFFFFFFF bs

  -- Durably append one CRC-framed record `<byteLen>:<crc32>:<payload>` + fsync;
  -- on first create also fsync the parent directory.
  appendWalRecordHS :: T.Text -> T.Text -> IO ()
  appendWalRecordHS path payload = do
    let pbytes = encodeUtf8 payload
        rec    = BC.pack (show (BS.length pbytes) ++ ":" ++ show (walCrc32 pbytes) ++ ":") <> pbytes
    existed <- doesFileExist (T.unpack path)
    withBinaryFile (T.unpack path) AppendMode $ \h -> do
      BS.hPut h rec
      hFlush h
      fd <- handleToFd h
      fileSynchronise fd
      closeFd fd
    when (not existed) (syncPathDirHS path)

  walIsDigit :: Word8 -> Bool
  walIsDigit w = w >= 48 && w <= 57

  walDigitsToInteger :: BS.ByteString -> Integer
  walDigitsToInteger = BS.foldl' (\a w -> a * 10 + toInteger (w - 48)) 0

  -- Byte-level record reader: Just (complete record payloads, torn tail dropped);
  -- Nothing = corruption (bad header / over-long digit run / CRC mismatch on a
  -- fully-present record). Missing/unreadable file → Just [].
  readWalRecordsHS :: T.Text -> IO (Maybe [T.Text])
  readWalRecordsHS path = do
    r <- Ex.try (BS.readFile (T.unpack path)) :: IO (Either Ex.SomeException BS.ByteString)
    pure $ case r of
      Left _   -> Just []
      Right bs -> walGo bs []
    where
      walGo bs acc
        | BS.null bs = Just (reverse acc)
        | otherwise =
            case BS.elemIndex 0x3a bs of
              Nothing -> if BS.all walIsDigit bs then Just (reverse acc) else Nothing
              Just i  ->
                let lenD   = BS.take i bs
                    afterL = BS.drop (i + 1) bs
                in if BS.null lenD || not (BS.all walIsDigit lenD) || BS.length lenD > 18
                   then Nothing
                   else case BS.elemIndex 0x3a afterL of
                          Nothing -> if BS.all walIsDigit afterL then Just (reverse acc) else Nothing
                          Just j  ->
                            let crcD = BS.take j afterL
                                rest = BS.drop (j + 1) afterL
                                n    = fromInteger (walDigitsToInteger lenD) :: Int
                            in if BS.null crcD || not (BS.all walIsDigit crcD) || BS.length crcD > 10
                               then Nothing
                               else if BS.length rest < n
                                    then Just (reverse acc)
                                    else let payload = BS.take n rest
                                             more    = BS.drop n rest
                                         in if toInteger (walCrc32 payload) == walDigitsToInteger crcD
                                            then walGo more (decodeUtf8With lenientDecode payload : acc)
                                            else Nothing
  #-}

------------------------------------------------------------------------
-- IO combinators
------------------------------------------------------------------------

infixl 1 _>>=_ _>>_

postulate
  _>>=_ : ∀ {A B : Set} → IO A → (A → IO B) → IO B
  _>>_  : ∀ {A B : Set} → IO A → IO B → IO B
  pure  : ∀ {A : Set} → A → IO A

{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC _>>_  = \_ _ -> (>>)  #-}
{-# COMPILE GHC pure  = \_ -> return  #-}

-- | Abort the process loudly (WAL recovery hits mid-log corruption).
postulate
  die : ∀ {A : Set} → String → IO A
{-# COMPILE GHC die = \_ msg -> ioError (userError (T.unpack msg)) #-}

-- | Try an IO action, catching all exceptions as nothing.
postulate
  tryCatch : ∀ {A : Set} → IO A → IO (Maybe A)
{-# COMPILE GHC tryCatch = \_ -> tryCatchImpl #-}

------------------------------------------------------------------------
-- MVar + exception-safe read-modify-write
------------------------------------------------------------------------

postulate
  MVar     : Set → Set
  newMVar  : ∀ {A : Set} → A → IO (MVar A)
  readMVar : ∀ {A : Set} → MVar A → IO A
{-# COMPILE GHC MVar     = type MVar.MVar #-}
{-# COMPILE GHC newMVar  = \_ -> MVar.newMVar  #-}
{-# COMPILE GHC readMVar = \_ -> MVar.readMVar #-}

-- native Haskell 2-tuple at the FFI boundary (Agda's Σ can't appear in a
-- COMPILE GHC type); modifyMVarMasked's callback returns IO (newState, result).
postulate
  Pair2   : Set → Set → Set
  mkPair2 : ∀ {A B : Set} → A → B → Pair2 A B
{-# COMPILE GHC Pair2   = type (,)    #-}
{-# COMPILE GHC mkPair2 = \_ _ -> (,) #-}

-- | Take the MVar, run the callback ASYNC-MASKED; on success put the returned new
-- state and yield the result; on ANY exception (incl. forcing a pure callback)
-- restore the original value and re-raise. Durable-before-visible: the callback
-- does its durable write before returning the new state that is then published.
postulate
  modifyMVarMasked : ∀ {A B : Set} → MVar A → (A → IO (Pair2 A B)) → IO B
{-# COMPILE GHC modifyMVarMasked = \_ _ -> MVar.modifyMVarMasked #-}

------------------------------------------------------------------------
-- Durable WAL file operations (byte-framed, CRC-checked)
------------------------------------------------------------------------

postulate
  -- durable overwrite (write+flush+fsync)
  writeFileText   : String → String → IO ⊤
  -- durably append one byte-length+CRC-framed record (+ dir fsync on create)
  appendWalRecord : String → String → IO ⊤
  -- read byte-framed records: just (complete payloads, torn tail dropped)
  --                            nothing (corruption → caller refuses to start)
  readWalRecords  : String → IO (Maybe (List String))

{-# COMPILE GHC writeFileText   = durableWriteHS WriteMode #-}
{-# COMPILE GHC appendWalRecord = appendWalRecordHS        #-}
{-# COMPILE GHC readWalRecords  = readWalRecordsHS         #-}
