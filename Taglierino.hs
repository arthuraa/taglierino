{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists, ExtendedDefaultRules #-}

{-|

Taglierino is a domain-specific language for modeling cryptographic protocols.
It allows us to define the behavior of agents that exchange messages in a
network, and to specify the security properties that the protocol should
satisfy.  The code is compiled down to finite labeled transition systems (LTSs)
that can be analyzed by the LTSA model checker
(<https://www.doc.ic.ac.uk/ltsa/>).

Taglierino follows the so called /Dolev-Yao/, or /symbolic/ model of
cryptography, in which the network is assumed to be controlled by an attacker
who is free to manipulate messages arbitrarily, but is not capable of breaking
cryptographic primitives or guess secrets out of thin air.  Thus, the attacker
can only decrypt a message if he knows the corresponding key.

-}

module Taglierino (
  -- * Terms and Processes
  --
  -- | Agents in Taglierino manipulate elements of the 'Term' type.  To write
  -- the code of an agent, use the 'Proc' monad.  The 'System' monad is used to
  -- put agents together to define an entire protocol, and also to issue
  -- compilation directives.
    Term
  , Proc
  , System
  , Agent

  -- * Term Generation
  , NewNonce
  , newNonce
  , NewConst
  , newConst
  , NewAKey
  , newAKey
  , NewSKey
  , newSKey
  , NewSigKey
  , newSigKey

  -- * Communication with the Network
  , send, receive

  -- * Long-term Storage
  , insertFresh

  -- * Term Manipulation
  , tup, untup
  , sign, checkSig, checkSign
  , pkey
  , aenc, senc
  , adec, sdec
  , hash
  , hmac
  , hkdf_extract, hkdf_expand
  , aead_enc, aead_dec
  -- ** Diffie-Hellman
  , expBase, expo

  -- * Correspondence events
  , begin, end

  -- * Protocol Definition
  , mkAgent, agentName
  , agent, store

  -- ** Specifying Attacker Knowledge
  --
  -- | Taglierino targets a /bounded/ model checker.  When generating an
  -- automaton, you must place a bound on what messages the attacker can learn,
  -- and how many of them.  The following functions are used for this purpose.
  , allow
  , knowledgeSize
  , public

  -- ** Correspondence queries
  , EventId
  , events
  , injective
  , nonInjective

  -- * Compilation
  , MonadOptions
  , options
  , Options(..)
  , defaultOptions
  , compileWith
  , compile
  ) where

import qualified Taglierino.LTS as LTS

import Prelude hiding (fail)
import qualified Prelude

import Data.Foldable
import Data.Char
import Data.List (intersperse, tails, isPrefixOf)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.MultiSet as MS
import Data.Text.Prettyprint.Doc
import qualified Data.Dequeue as Q
import qualified Data.PQueue.Prio.Min as PQ
import Data.Maybe (isJust)

import System.IO
import Control.Monad (forM, forM_)
import Control.Monad.Fail
import Control.Monad.Cont   hiding (fail)
import Control.Monad.State  hiding (fail)
import Control.Monad.Reader hiding (fail)

import qualified GHC.Exts as Exts

data Id = Id (Maybe Agent) Int
  deriving (Eq, Ord, Show)

instance Pretty Id where
  pretty (Id Nothing i) = pretty i
  pretty (Id (Just a) i) = pretty i <> brackets (pretty a)

type Set a      = S.Set a
type Map a b    = M.Map a b
type Queue a    = Q.BankersDequeue a
type PQueue k a = PQ.MinPQueue k a
type Nonce      = Id
type AKey       = Id
type SKey       = Id
type SigKey     = Id
type Const      = Id

data KeyType = Public | Private
  deriving (Show, Eq, Ord)

type EventId = String

-- | Options that control the output of Taglierino (cf. 'compileWith').
data Options = Options { oPrintHeaders    :: Bool
                       -- ^ Print a header explaining which terms and events
                       -- each label represents.  Useful for interpreting
                       -- counterexamples in LTSA and for using assumption
                       -- learning.
                       , oPrintErrors     :: Bool
                       -- ^ Print error messages raised by the agents as
                       -- comments in the LTSA model.  Useful for debugging
                       -- agent code.
                       , oPrintMessages   :: Bool
                       -- ^ Print the meaning of each number that represents a
                       -- message in the LTSA model.  Useful for debugging, but
                       -- can significantly increase the size of the output.
                       , oPrintKnowledge  :: Bool
                       -- ^ Similar to 'oPrintMessages', but for codes that
                       -- represent the attacker knowledge.
                       , oVerboseMessages :: Bool
                       -- ^ Similar to 'oPrintMessages', but instead of using
                       -- numbers to represent messages, use structured labels
                       -- that are easier to read (e.g. @akey.0.priv@).  LTSA
                       -- provides limited support for manipulating these
                       -- structured labels, which can be helpful when
                       -- specifying sets of messages (e.g. for alphabet
                       -- refinement).  Unfortunately, this representation can
                       -- also slow down the model checker, so use this feature
                       -- with care.
                       , oOutputFile      :: Maybe FilePath
                       -- ^ If present, save the output in the given file.  If
                       -- absent, print the output to @stdout@.
                       }
  deriving (Eq, Ord, Show)

-- | Default compilation options
defaultOptions :: Options
defaultOptions = Options False False False False False Nothing

-- | Terms manipulated by agents and the attacker.  The representation of the
-- type is kept opaque to highlight the legal operations of the symbolic model.
data Term = Nonce Nonce
          | Tup [Term]
          | AKey AKey KeyType
          | SigKey SigKey KeyType
          | SKey SKey
          | AEnc AKey Term
          | Sign SigKey Term
          | SEnc SKey Term
          | Const Const
          | Exp (MS.MultiSet Term)
          | Hash Term
          | AEAD Term Term Term Term
          | Garbage
  deriving (Eq, Ord, Show)

labelOfId :: Id -> [LTS.LabelPart]
labelOfId (Id Nothing i)  = [LTS.const i]
labelOfId (Id (Just a) i) = [agentLabel a, LTS.const i]

labelOfKeyType :: KeyType -> [LTS.LabelPart]
labelOfKeyType Private = [LTS.Simple "priv"]
labelOfKeyType Public  = [LTS.Simple "pub"]

-- | Represent a message as a structured LTSA label rather than a number.
labelOfTerm' :: Term -> [LTS.LabelPart]
labelOfTerm' t = go t
  where go :: Term -> [LTS.LabelPart]
        go (Nonce n)   = [LTS.Simple "n"] ++ labelOfId n
        go (Tup ts)    = [LTS.Simple "t"]
                         ++ concat (intersperse [LTS.Simple "comma"] (map go ts))
                         ++ [LTS.Simple "dot"]
        go (AKey k ty) = [LTS.Simple "akey"] ++ labelOfId k ++ labelOfKeyType ty
        go (SigKey k ty) = [LTS.Simple "sigkey"] ++ labelOfId k ++ labelOfKeyType ty
        go (SKey k) = [LTS.Simple "skey"] ++ labelOfId k
        go (AEnc k t) = [LTS.Simple "aenc"] ++ labelOfId k ++ go t
        go (Sign k t) = [LTS.Simple "sig"] ++ labelOfId k ++ go t
        go (SEnc k t) = [LTS.Simple "senc"] ++ labelOfId k ++ go t
        go (Const c)  = [LTS.Simple "c"] ++ labelOfId c
        go (Exp ex)   = [LTS.Simple "exp"]
                        ++ concat (intersperse ([LTS.Simple "p"])
                                   [ [LTS.const i, LTS.Simple "x"] ++ go t
                                   | (t, i) <- occurrences ex])
                        ++ [LTS.Simple "dot"]
        go (Hash t)   = [LTS.Simple "hash"] ++ go t
        go (AEAD t1 t2 t3 t4) = [LTS.Simple "aead"]
                                ++ concat (intersperse [LTS.Simple "comma"] $ map go [t1, t2, t3, t4])
                                ++ [LTS.Simple "dot"]
        go Garbage = [LTS.Simple "g"]

-- | Output a term as an LTSA label.  The options control whether the term index
-- is used (cf. 'oVerboseMessages') or not.
labelOfTerm :: Options -- ^ Compilation options
            -> Term    -- ^ Term to serialize
            -> Int     -- ^ Term index
            -> [LTS.LabelPart]
labelOfTerm opts t ti
  | oVerboseMessages opts = labelOfTerm' t
  | oPrintMessages opts   = [LTS.Int $ LTS.Const ti $ Just $ show $ pretty t]
  | otherwise             = [LTS.const ti]

prettyTerm :: Pretty a => Int -> a -> Doc ann
prettyTerm 1 x = pretty x
prettyTerm i x = pretty i <+> pretty "*" <+> pretty x

-- | Convert a multiset to an association list
occurrences :: (Ord a) => MS.MultiSet a -> [(a, Int)]
occurrences ms =
  [(x, MS.occur x ms) | x <- MS.distinctElems ms]

-- | Print a multiset as a sum (e.g., @{x, x, y}@ becomes @2*x + y@)
prettySum :: (Ord a, Pretty a) => MS.MultiSet a -> Doc ann
prettySum ms
  | MS.null ms = pretty "0"
  | otherwise  =
    concatWith (surround (space <> pretty "+" <> space))
    $ [prettyTerm i x | (x,i) <- occurrences ms]

newtype Agent = Agent String
  deriving (Eq, Ord, Show, Pretty)

reservedNames :: [String]
reservedNames =
  ["Attacker", "System", "Check", "ENVIRONMENT"]

reservedPrefixes :: [String]
reservedPrefixes =
  ["Def_", "Check_", "Store_"]

-- | Create an agent name.  Note that the name has to be a valid LTSA process
-- identifier: it must begin with a capital letter, and is restricted to
-- alphanumeric characters.
mkAgent :: String -> Agent
mkAgent [] = error "Agent name cannot be empty"
mkAgent a@(c : s)
  | not $ isAsciiUpper c =
    error $ "Agent name begin with an upper-case letter (given " ++ a ++ ")"
  | not $ all (\c' -> isAscii c' && isAlphaNum c') s =
    error $ "Agent name must only have alphanumeric characters (given " ++ a ++ ")"
  | a `elem` reservedNames =
    error $ "The identifier \"" ++ a ++ "\" is reserved"
  | any (`isPrefixOf` a) reservedPrefixes =
    error $ "The identifier \"" ++ a ++ "\" begins with a reserved prefix"
  | otherwise =
    Agent a

-- | String represtation of the agent name.
agentName :: Agent -> String
agentName (Agent a) = a

agentLabel :: Agent -> LTS.LabelPart
agentLabel (Agent []) = error "An agent with an empty name was created"
agentLabel (Agent (c : s)) = LTS.Simple $ toLower c : s

instance Pretty Term where
  pretty (Nonce n) = pretty "N" <> pretty n
  pretty (Tup ms)  = parens $ align $ sep $ punctuate comma $ map pretty ms
  pretty (AKey k Public) = pretty "PK" <> pretty k
  pretty (AKey k Private) = pretty "SK" <> pretty k
  pretty (SigKey k Public) = pretty "SPK" <> pretty k
  pretty (SigKey k Private) = pretty "SSK" <> pretty k
  pretty (SKey k) = pretty "K" <> pretty k
  pretty (AEnc k m) = pretty "A" <> braces (pretty m) <> pretty "@" <> pretty k
  pretty (Sign k m) = pretty "Sign" <> braces (pretty m) <> pretty "@" <> pretty k
  pretty (SEnc k m) = pretty "S" <> braces (pretty m) <> pretty "@" <> pretty k
  pretty (Const c) = pretty "C" <> pretty c
  pretty (Exp ms) = pretty "Exp" <> parens (prettySum ms)
  pretty (Hash m) = pretty "Hash" <> braces (pretty m) 
  pretty (AEAD m1 m2 m3 m4) = pretty "AEAD" <> pretty (Tup [m1, m2, m3, m4])
  pretty Garbage = pretty "Garbage"

instance Exts.IsList Term where
  type Item Term = Term
  fromList = Tup
  toList (Tup xs) = xs
  toList m = fail $ "Not a tuple: " ++ show (pretty m)

-- | Class for monads that allow generating fresh nonces.  It is more convenient
-- to generate nonces in the 'System' monad, since we can mention the nonces
-- when declaring the allowed set of messages of the network (cf. 'allow').
-- However, 'Proc' is also an instance of this class.
class NewNonce m where
  newNonce :: m Term

-- | Similar to 'NewNonce', but for constants (typically agent names).
class NewConst m where
  newConst :: m Term

-- | Similar to 'NewNonce', but for asymmetric keys.
class NewAKey m where
  newAKey :: m Term

-- | Similar to 'NewNonce', but for symmetric keys.
class NewSKey m where
  newSKey :: m Term

-- | Similar to 'NewNonce', but for signature keys.
class NewSigKey m where
  newSigKey :: m Term

-- | Monads that allow reading compilation options.
class MonadOptions m where
  options :: m Options

-- | Read-only state of a process.  Most of it is determined by options set in
-- the 'System' monad.
data ProcRState = ProcRState { psAllowed :: S.Set Term
                             -- ^ Allowed terms in the network
                             , psEvents  :: S.Set Term
                             -- ^ Allowed events in the network
                             , psStore :: S.Set Term
                             -- ^ Terms that can be stored by the agent
                             , psAgent   :: Agent
                             -- ^ The name of the agent
                             , psThread  :: Int
                             -- ^ The number of the current thread
                             , psOptions :: Options
                             -- ^ Compilation options
                             }
  deriving (Eq, Ord)

-- | Writable state of a process, which tracks how many fresh cryptographic
-- entities it has generated.
data ProcState = ProcState { psNonces  :: Int
                           , psAKeys   :: Int
                           , psSKeys   :: Int
                           , psSigKeys :: Int
                           , psConsts  :: Int }
  deriving (Eq, Ord)

-- | The 'Proc' monad is used for defining the behavior of agents in a network.
-- Internally, it builds the body of the corresponding LTS in
-- continuation-passing style, which simplifies the implementation of
-- non-deterministic primitives such as 'receive' and 'insertFresh'.
newtype Proc a =
  Proc (ContT LTS.Body (ReaderT ProcRState (State ProcState)) a)

deriving instance Functor Proc
deriving instance Applicative Proc
deriving instance Monad Proc
deriving instance MonadReader ProcRState Proc
deriving instance MonadState ProcState Proc

instance MonadOptions Proc where
  options = reader psOptions

-- | Failure in the 'Proc' monad simply causes the process to stop; the error
-- message can be shown in the final output for debugging purposes
-- (cf. 'oPrintErrors').
instance MonadFail Proc where
  fail m = do
    printErrors <- oPrintErrors <$> options
    let ann = if printErrors then Just m else Nothing
    Proc $ ContT $ \_ -> return $ LTS.Name $ LTS.STOP ann

instance NewNonce Proc where
  newNonce = do
    ProcRState{..} <- ask
    ProcState{..}  <- get
    put $ ProcState{psNonces = psNonces + 1, ..}
    return $ Nonce $ Id (Just psAgent) psNonces

instance NewConst Proc where
  newConst = do
    ProcRState{..} <- ask
    ProcState{..}  <- get
    put $ ProcState{psConsts = psConsts + 1, ..}
    return $ Nonce $ Id (Just psAgent) psConsts

instance NewAKey Proc where
  newAKey = do
    ProcRState{..} <- ask
    ProcState{..}  <- get
    put $ ProcState{psAKeys = psAKeys + 1, ..}
    return $ Nonce $ Id (Just psAgent) psAKeys

instance NewSKey Proc where
  newSKey = do
    ProcRState{..} <- ask
    ProcState{..}  <- get
    put $ ProcState{psSKeys = psSKeys + 1, ..}
    return $ Nonce $ Id (Just psAgent) psSKeys

instance NewSigKey Proc where
  newSigKey = do
    ProcRState{..} <- ask
    ProcState{..}  <- get
    put $ ProcState{psSigKeys = psSigKeys + 1, ..}
    return $ Nonce $ Id (Just psAgent) psSigKeys

-- | A primitive process that simply emits a label.  Used internally to define
-- higher-level primitives.
action :: LTS.Label -> Proc ()
action l =
  Proc
  $ mapContT (\k -> (\res -> LTS.Body [LTS.Action l res]) <$> k) $ return ()

sendL :: [LTS.LabelPart] -> LTS.Label
sendL args = LTS.Label $ [LTS.Simple "send"] ++ args

-- | Send a message if it belongs to the allowed set, otherwise fails.
send :: Term -> Proc ()
send m = do
  ProcRState{..} <- ask
  case S.lookupIndex m psAllowed of
    Just mi ->
      action $ sendL $ [agentLabel psAgent, LTS.const psThread]
      ++ labelOfTerm psOptions m mi
    Nothing -> fail $ show $ pretty "Not allowed to send" <+> pretty m

beginL :: EventId -> [LTS.LabelPart] -> LTS.Label
beginL e args =
  LTS.Label $ [LTS.Simple "begin", LTS.Simple e] ++ args

-- | Emit a begin event if it belongs to the set of allowed events, otherwise
-- fails.
begin :: EventId -- ^ Name of the event
      -> Term    -- ^ Data item associated with the event
      -> Proc ()
begin e m = do
  ProcRState{..} <- ask
  case S.lookupIndex m psEvents of
    Just mi ->
      action $ beginL e $ [agentLabel psAgent, LTS.const psThread]
      ++ labelOfTerm psOptions m mi
    Nothing -> fail $ show $ pretty "Not allowed to emit" <+> pretty m

endL :: EventId -> [LTS.LabelPart] -> LTS.Label
endL e args =
  LTS.Label $ [LTS.Simple "end", LTS.Simple e] ++ args

-- | Emit an end event if it belongs to the set of allowed events, otherwise
-- fails.  (cf. 'query')
end :: EventId -- ^ Name of the event
    -> Term    -- ^ Data item associated with the event
    -> Proc ()
end e m = do
  ProcRState{..} <- ask
  case S.lookupIndex m psEvents of
    Just mi ->
      action $ endL e $ [agentLabel psAgent, LTS.const psThread]
      ++ labelOfTerm psOptions m mi
    Nothing -> fail $ show $ pretty "Not allowed to emit" <+> pretty m

receiveL :: [LTS.LabelPart] -> LTS.Label
receiveL args = LTS.Label $ [LTS.Simple "receive"] ++ args

-- | Receive a message from the network.  Internally, this function simply
-- composes the continuation processes in parallel evaluated at each message
-- that the process might receive.
receive :: Proc Term
receive = do
  ProcRState{..} <- ask
  Proc $ ContT $ \k -> do
    -- Save the state of the agent so that each invokation of the continuation
    -- uses the same initial state.
    s <- get
    actions <- forM (zip [0 ..] $ S.toList psAllowed) $ \(mi, m) -> do
      put s
      body <- k m
      let l = receiveL $ [agentLabel psAgent, LTS.const psThread]
              ++ labelOfTerm psOptions m mi
      return $ LTS.Action l body
    return $ LTS.Body actions

insertFreshL :: [LTS.LabelPart] -> LTS.Label
insertFreshL args = LTS.Label $ [LTS.Simple "insertfresh"] ++ args

-- | Store a term in the agent's permanent storage.  The returned boolean
-- indicates whether the term was already present in the storage.
insertFresh :: Term -> Proc Bool
insertFresh r = do
  ProcRState{..} <- ask
  case S.lookupIndex r psAllowed of
    Just mi | S.member r psStore ->
      Proc $ ContT $ \k -> do
        -- Save the state of the agent so that each invokation of the continuation
        -- uses the same initial state.
        s <- get
        actions <- forM [True, False] $ \m -> do
          put s
          body <- k m
          let mm = if m then "true" else "false"
          let l = insertFreshL $ [agentLabel psAgent, LTS.const psThread] ++
                  labelOfTerm psOptions r mi ++ [LTS.Simple mm]
          return $ LTS.Action l body
        return $ LTS.Body actions
    _ -> fail $ show $ pretty "Not allowed to insert fresh"
         <+> pretty r
         <+> pretty " in "
         <+> pretty (LTS.Simple (agentName psAgent)) <+> pretty "'s storage"

-- | Encrypt a term with an asymmetric encryption key.  If encryption fails, an
-- opaque, useless term is returned.
aenc :: Term -- ^ Encryption key
     -> Term -- ^ Term to be encrypted
     -> Term
aenc (AKey k Public) m = AEnc k m
aenc _ _ = Garbage

decryptFail :: Term -> Term -> Proc a
decryptFail m1 m2 =
  fail $ show $ pretty "Decryption failed:" <+> pretty m1 <+> pretty m2

checkSignFail :: Term -> Term -> Proc a
checkSignFail m1 m2 =
  fail $ show $ pretty "check signature failed:" <+> pretty m1 <+> pretty m2

-- | Attempt to decrypt a term with an asymmetric decryption key.
adec :: Term -- ^ Decryption key
     -> Term -- ^ Encrypted message
     -> Proc Term
adec m1@(AKey k1 Private) m2@(AEnc k2 m) =
  if k1 == k2 then return m
  else decryptFail m1 m2
adec m1 m2 = decryptFail m1 m2

-- | Encrypt a message with a symmetric key.  If encryption fails, an opaque,
-- useless term is returned.
senc :: Term -- ^ Key
     -> Term -- ^ Message to be encrypted
     -> Term
senc (SKey k) m = SEnc k m
senc _ _ = Garbage

-- | Decrypt a message with a symmetric key.
sdec :: Term -- ^ Key
     -> Term -- ^ Encrypted message
     -> Proc Term
sdec m1@(SKey k1) m2@(SEnc k2 m) =
  if k1 == k2 then return m
  else decryptFail m1 m2
sdec m1 m2 = decryptFail m1 m2

-- | Sign a message.  If the signature fails, an opaque, useless term is
-- returned.
sign :: Term -- ^ Signature key
     -> Term -- ^ Term to sign
     -> Term
sign (SigKey k Private) m = Sign k m
sign _ _ = Garbage

-- | Extract a public key from a private key.  Works for encryption keys and
-- signature keys.
pkey :: Term -> Term
pkey (SigKey k Private) = SigKey k Public
pkey (AKey k Private)   = AKey k Public
pkey m = error $ "Not a private key: " ++ show (pretty m)

-- | Check a digital signature using a verification key.
checkSig :: Term -- ^ Verification key
         -> Term -- ^ Signature
         -> Term -- ^ Term to check
         -> Proc Bool
checkSig (SigKey k1 Public) (Sign k2 m2) m3 =
  return (k1 == k2 && m2 == m3)
checkSig _ _ _ = return False

-- | Extract the signed term from a digital signature.
checkSign :: Term -- ^ Verification key
          -> Term -- ^ Signed message
          -> Proc Term
checkSign m1@(SigKey k1 Public) m2@(Sign k2 m) =
  if k1 == k2 then return m
  else checkSignFail m1 m2 
checkSign m1 m2 = checkSignFail m1 m2

expBase :: Term
expBase = Exp MS.empty

expo :: Term -> Term -> Term
expo (Exp ms) m = Exp $ MS.insert m ms
expo _ _ = Garbage

hash :: Term -> Term
hash = Hash

hmac :: Term -> Term -> Term -> Term -> Term
hmac key text ipad opad =
  Hash [[key, opad], Hash [[key, ipad], text]]

hkdf_extract :: Term -> Term -> Term -> Term -> Term
hkdf_extract salt ikm ipad opad = 
  let tup1 = Tup [salt, opad]
      tup2 = Tup [salt, ipad] in
    let tup3 = Tup [tup2, ikm] in
      let inner = Hash tup3 in
        let tup4 = Tup [ tup1, inner ] in
          Hash tup4
      
hkdf_expand :: Term -> Term -> Term -> Term -> Term -> Term
hkdf_expand prk info l ipad opad = 
  let tup1 = Tup [prk, opad]
      tup2 = Tup [prk, ipad]
      tup3 = Tup [info, l] in
    let tup4 = Tup [tup2, tup3] in
      let inner = Hash tup4 in
        let tup5 = Tup [ tup1, inner] in
          Hash tup5

aead_enc :: Term -> Term -> Term -> Term -> Term
aead_enc m1 m2 m3 m4 = AEAD m1 m2 m3 m4

aead_dec :: Term -> Term -> Term -> Term -> Proc Term
aead_dec m1 m2 m3@(AEAD m1' m2' m3' m4') m4 =
  if (m1==m1' && m2 == m2'&& m4 == m4') then return m3'
  else decryptFail m1 m3
aead_dec m1 _ m3 _  = decryptFail m1 m3

-- | Pack a list of messages into a tuple.
tup :: [Term] -> Term
tup = Tup

-- | Attempt to unpack a message as a list of messages.
untup :: (Monad m, MonadFail m) => Term -> m [Term]
untup (Tup ms) = return ms
untup m = fail $ show $ pretty "Not a tuple:" <+> pretty m

-- | Run a process to build an automaton, given suitable arguments.
runProc :: Proc ()    -- ^ Process to run
        -> S.Set Term -- ^ Allowed message terms
        -> S.Set Term -- ^ Allowed event terms
        -> S.Set Term -- ^ Terms that the agent can store
        -> Agent      -- ^ Agent identifier
        -> Int        -- ^ Thread identifier
        -> Options    -- ^ Compilation options
        -> LTS.Body
runProc (Proc f) psAllowed psEvents psStore psAgent psThread psOptions =
  let stop = return $ LTS.Name $ LTS.STOP Nothing
      rst = ProcRState{..}
      wst = ProcState 0 0 0 0 0
      (res, _) = runState (runReaderT (runContT f $ const stop) rst) wst
  in res

-- | Type of correspondence query to produce.
data Property = NonInjective
              -- ^ Each 'end' event can match multiple 'begin' events
              | Injective
              -- ^ Each 'end' event must match exactly one 'begin'
  deriving (Eq, Ord)

data Query = Query { qBegin :: Agent
                   , qEnd   :: Agent
                   , qProp  :: Property }
  deriving (Eq, Ord)

-- | Internal compiler state
data SystemState = SystemState { sNonces :: Int
                               -- ^ Number of nonces generated in the model
                               , sAKeys  :: Int
                               -- ^ Number of asymmetric keys generated
                               , sSKeys  :: Int
                               -- ^ Number of symmetric keys generated
                               , sSigKeys :: Int
                               -- ^ Number of signature keys generated
                               , sConsts :: Int
                               -- ^ Number of constants generated
                               , sEvents  :: S.Set Term
                               -- ^ Set of allowed event terms
                               , sAllowed :: S.Set Term
                               -- ^ Set of allowed message terms
                               , sPublic  :: S.Set Term
                               -- ^ Set of public terms
                               , sStore   :: M.Map Agent (S.Set Term)
                               -- ^ Messages that each agent can store
                               , sKnowledgeSize :: Int
                               -- ^ How many messages the attacker can learn
                               -- from the network
                               , sOptions :: Options
                               -- ^ Compilation options
                               , sProcs   :: M.Map Agent (Queue (Proc ()))
                               -- ^ Agent definitions (each agent can run
                               -- multiple processes, hence the queue)
                               , sQueries :: Map EventId Query
                               -- ^ Type of query associated with each event
                               }

-- | The 'System' monad is used to specify global declarations for the process,
-- such as agent definitions, attacker parameters, etc.
newtype System a = System (State SystemState a)
  deriving (Functor, Applicative, Monad, MonadState SystemState)

instance MonadOptions System where
  options = do
    SystemState{..} <- get
    return sOptions

instance NewNonce System where
  newNonce = do
    SystemState {..} <- get
    put $ SystemState {sNonces = sNonces + 1, ..}
    return $ Nonce (Id Nothing sNonces)

instance NewConst System where
  newConst = do
    SystemState {..} <- get
    put $ SystemState {sConsts= sConsts + 1, ..}
    return $ Const (Id Nothing sConsts)


instance NewAKey System where
  newAKey = do
    SystemState {..} <- get
    put $ SystemState {sAKeys = sAKeys + 1, ..}
    return $ AKey (Id Nothing sAKeys) Private

instance NewSKey System  where
  newSKey = do
    SystemState {..} <- get
    put $ SystemState {sSKeys = sSKeys + 1, ..}
    return $ SKey (Id Nothing sSKeys)

instance NewSigKey System where
  newSigKey = do
    SystemState {..} <- get
    put $ SystemState {sSigKeys = sSigKeys + 1, ..}
    return $ SigKey (Id Nothing sSigKeys) Private

instance MonadFail System where
  fail msg = Prelude.fail msg

-- | Allow all terms in the list to be used as data items in events.
events :: [Term] -> System ()
events evs = do
  SystemState {..} <- get
  put $ SystemState {sEvents = sEvents `S.union` S.fromList evs, ..}

-- | Generate a query of a given type for an event id.
query :: EventId -> Query -> System ()
query id q = do
  SystemState {..} <- get
  put $ SystemState {sQueries = M.insert id q sQueries, ..}

-- | Declare a non-injective query
nonInjective :: EventId -- ^ The identifier of the event
             -> Agent   -- ^ The agent that triggers begin
             -> Agent   -- ^ The agent that triggers end
             -> System ()
nonInjective id qBegin qEnd =
  query id Query{ qProp = NonInjective, .. }

-- | Declare an injective query
injective :: EventId -- ^ The identifier of the event
          -> Agent   -- ^ The agent that triggers begin
          -> Agent   -- ^ The agent that triggers end
          -> System ()
injective id qBegin qEnd =
  query id Query{ qProp = Injective, .. }

-- | Allow all terms in the list to be exchanged in the network.
allow :: [Term] -> System ()
allow ms = do
  SystemState {..} <- get
  put $ SystemState {sAllowed = sAllowed `S.union` S.fromList ms, ..}

-- | Declare all terms in the list to be part of the initial attacker knowledge.
public :: [Term] -> System ()
public iks = do
  SystemState {..} <- get
  put $ SystemState {sPublic = sPublic `S.union` S.fromList iks, ..}

-- | Declare messages on the list as being storable by an agent.
store :: String -> [Term] -> System ()
store name rs = do
  let a = mkAgent name
  SystemState {..} <- get
  case M.lookup a sStore of
    Just terms ->
      put $
      SystemState
        {sStore = M.insert a (terms `S.union` S.fromList rs) sStore, ..}
    Nothing ->
      put $ SystemState {sStore = M.insert a (S.fromList rs) sStore, ..}

-- | Declare the maximum size of the attacker knowledge.
knowledgeSize :: Int -> System ()
knowledgeSize k = do
  SystemState{..} <- get
  put $ SystemState{sKnowledgeSize = k, ..}

-- | Declare the code that an agent will execute.  Each agent can run multiple
-- processes at a time; you just need to call 'agent' multiple times.
agent :: String -> Proc () -> System ()
agent a p = do
  SystemState {..} <- get
  let a' = mkAgent a
  let q  = M.findWithDefault Q.empty a' sProcs
  put $ SystemState {sProcs = M.insert a' (Q.pushBack q p) sProcs, ..}

-- | Compiler output
data Program =
  Program { pEvents        :: S.Set Term
          -- ^ Allowed event terms
          , pAllowed       :: S.Set Term
          -- ^ Allowed message terms
          , pPublic        :: S.Set Term
          -- ^ Public terms
          , pStore         :: M.Map Agent (S.Set Term)
          -- ^ Allowed terms in each agent's storage
          , pKnowledgeSize :: Int
          -- ^ Maximum size of attacker knowledge
          , pQueries       :: Map EventId Query
          -- ^ Type of each query.
          , pProcs         :: M.Map Agent [LTS.Body]
          -- ^ Automata generated for each agent
          }

-- | Generate the compiler output given a set of options
runSystem :: Options -> System () -> Program
runSystem opts (System f) =
  let initialState = SystemState { sNonces = 0
                                 , sAKeys  = 0
                                 , sSKeys  = 0
                                 , sSigKeys = 0
                                 , sConsts = 0
                                 , sEvents  = S.empty
                                 , sAllowed = S.empty
                                 , sPublic  = S.empty
                                 , sStore  = M.empty
                                 , sKnowledgeSize = 0
                                 , sOptions = opts
                                 , sProcs   = M.empty
                                 , sQueries = M.empty }
      ((), SystemState {..}) = runState f initialState
      run a id p =
        let psStore = M.findWithDefault S.empty a sStore
        in runProc p sAllowed sEvents psStore a id opts
      procs = M.mapWithKey (\a ps -> zipWith (run a) [0 ..] $ toList ps) sProcs
  in Program sEvents sAllowed sPublic sStore sKnowledgeSize sQueries procs

-- | Elementary messages are those that cannot be further decomposed by the
-- attacker.  Once the attacker knows an elementary message, there is nothing
-- else that can be extracted from it, whereas other messages might be further
-- analyzed to extract more knowledge once it increases.

elementary :: Term -> Bool
elementary (Nonce _)       = True
elementary (Tup _)         = False
elementary (AKey _ priv)   = priv == Private
elementary (SigKey _ priv) = priv == Private
elementary (SKey _)        = True
elementary (AEnc _ _)      = False
elementary (Sign _ _)      = False
elementary (SEnc _ _)      = False
elementary (Const _)       = True
elementary (Exp _)         = False
elementary (Hash _)        = False
elementary (AEAD _ _ _ _)  = False
elementary Garbage         = False

-- | Set of messages known by the attacker.  As an optimization, we ensure that
-- this set never contains a tuple, since knowing a tuple is equivalent to
-- knowing its components.  We also keep elementary terms separate from other
-- terms, since those do not have to be analyzed when the knowledge increases.
data Knowledge = Knowledge { kElem :: S.Set Term
                           -- ^ Elementary terms in the knowledge
                           , kTemp :: S.Set Term
                           -- ^ Non-elementary terms in the knowledge
                           }
  deriving (Eq, Ord)

instance Pretty Knowledge where
  pretty Knowledge{..} = pretty $ (S.toList kElem, S.toList kTemp)

kempty :: Knowledge
kempty = Knowledge S.empty S.empty

kunion :: Knowledge -> Knowledge -> Knowledge
kunion (Knowledge pk1 tk1) (Knowledge pk2 tk2) =
  Knowledge (S.union pk1 pk2) (S.union tk1 tk2)

kinsert :: Term -> Knowledge -> Knowledge
kinsert m Knowledge{..}
  | elementary m = Knowledge { kElem = S.insert m kElem, .. }
  | otherwise    = Knowledge { kTemp = S.insert m kTemp, .. }

ksingleton :: Term -> Knowledge
ksingleton m = kinsert m kempty

kmember :: Term -> Knowledge -> Bool
kmember m Knowledge{..}
  | elementary m = S.member m kElem
  | otherwise    = S.member m kTemp

-- | Attempt to factor a multiset as a union of multisets by doing a graph
-- search.  Used for minimizing the knowledge in the presence of Diffie-Hellman
-- terms.

factorMultiSet :: Ord a
               => [MS.MultiSet a] -- ^ Allowed factors
               -> MS.MultiSet a   -- ^ Multiset to be factored
               -> Maybe [Int]        -- ^ Coefficients for each multiset
factorMultiSet xs y = go xs y
  where go [] y
          | MS.null y = Just []
          | otherwise = Nothing
        go xs@(x : xs') y
          | MS.isSubsetOf x y =
            case go xs (y MS.\\ x) of
              Just (cx : cxs') -> Just (cx + 1 : cxs')
              _                -> fmap (0 :) (go xs' y)
          | otherwise =
            fmap (0 :) (go xs' y)

-- | @knows m knw@ returns @True@ if and only if the attacker can produce the
-- message @m@ using the knowledge @knw@.

knows :: Term -> Knowledge -> Bool
knows m@(Nonce _) knw = kmember m knw
knows m@(Const _) knw = kmember m knw
knows m@(AKey k priv) knw =
  kmember m knw
  || priv == Public && kmember (AKey k Private) knw
knows m@(SigKey k priv) knw =
  kmember m knw
  || priv == Public && kmember (SigKey k Private) knw
knows m@(SKey _) knw = kmember m knw
knows (Tup ms) knw = all (flip knows knw) ms
knows m@(AEnc k m') knw =
  kmember m knw
  || knows (AKey k Public) knw && knows m' knw
knows m@(Sign k m') knw =
  kmember m knw
  || knows (SigKey k Private) knw && knows m' knw
knows m@(SEnc k m') knw =
  kmember m knw
  || knows (SKey k) knw && knows m' knw
knows (Exp ms) knw =
  let exps    = [ms' | Exp ms' <- S.toList $ kTemp knw]
      singles = [MS.singleton m | m <- MS.distinctElems ms, knows m knw] in
    isJust $ factorMultiSet (exps ++ singles) ms
knows m@(Hash m') knw =
  kmember m knw || knows m' knw
knows (AEAD m1 m2 m3 m4) knw =
  -- TODO: Can we simplify this?
  kmember (AEAD m1 m2 m3 m4) knw
  || all (flip knows knw) [m1, m2, m3, m4]
knows Garbage _ = False

knull :: Knowledge -> Bool
knull Knowledge{..} = S.null kElem && S.null kTemp

-- | @extractKnowledge m knw@ produces that can be learned from @m@ and @knw@,
-- except those that were already known in @knw@ alone.
--
-- This function should respect the following invariant: if it returns a
-- nonempty set @knw'@, then @kunion (kremove knw m) knw' == kinsert m knw@.
extractKnowledge :: Term -> Knowledge -> Knowledge
extractKnowledge m@(Nonce _) knw = extractKnowledge1 m knw
extractKnowledge m@(Const _) knw = extractKnowledge1 m knw
extractKnowledge m@(AKey _ _) knw = extractKnowledge1 m knw
extractKnowledge m@(SigKey _ _) knw = extractKnowledge1 m knw
extractKnowledge m@(SKey _) knw = extractKnowledge1 m knw
extractKnowledge (Tup ms) knw = foldl kunion kempty [extractKnowledge m knw | m <- ms]
extractKnowledge m@(AEnc k m') knw =
  let knw1 = extractKnowledge1 m knw
      knw2 = if knows (AKey k Private) knw then extractKnowledge m' knw
             else kempty in
    kunion knw1 knw2
extractKnowledge m@(Sign _ m') knw =
  let knw1 = extractKnowledge1 m knw
      knw2 = extractKnowledge m' knw in
    kunion knw1 knw2
extractKnowledge m@(SEnc k m') knw =
  let knw1 = extractKnowledge1 m knw
      knw2 = if knows (SKey k) knw then extractKnowledge m' knw
             else kempty in
    kunion knw1 knw2
extractKnowledge m@(Exp _) knw = extractKnowledge1 m knw
extractKnowledge m@(Hash _) knw = extractKnowledge1 m knw
extractKnowledge m@(AEAD m1 m2 m3 m4) knw =
  let knw1 = extractKnowledge1 m knw
      knw2 = if all (flip knows knw) [m1, m2, m4] then extractKnowledge m3 knw
             else kempty in
    kunion knw1 knw2
extractKnowledge Garbage _ = kempty

-- | A special case of @extractKnowledge@ that does not traverse subterms.
extractKnowledge1 :: Term -> Knowledge -> Knowledge
extractKnowledge1 m knw
  | knows m knw = kempty
  | otherwise   = ksingleton m

knormalize :: Knowledge -> Knowledge
knormalize knw =
  let extracts = M.fromSet (flip extractKnowledge knw) (kTemp knw)
      addMsg (acc, redo) m knw'
        | knull knw' = (kinsert m acc, redo)
        | otherwise  = (kunion acc knw', True)
      init           = (Knowledge (kElem knw) S.empty, False)
      (knw', redo)   = M.foldlWithKey addMsg init extracts in
    if redo then knormalize knw' else knw'

-- | @updKnowledge m knw@ adds to @knw@ all the knowledge that can be learned
-- from @m@ and @knw@.
updKnowledge :: Term -> Knowledge -> Knowledge
updKnowledge m knw =
  let knw' = extractKnowledge m knw in
    if knull knw' then knw
    else knormalize (kunion knw knw')

knowledgeOfSet :: S.Set Term -> Knowledge
knowledgeOfSet ms =
  let (kElem, kTemp) = S.partition elementary ms in
    knormalize Knowledge{..}

-- The attacker body maps each possible knowledge to the transitions that can be
-- made from that knowledge.
type AttackerBody = M.Map Knowledge [(Term, Knowledge)]

-- | Generate the attacker automaton
attacker :: Options  -- ^ Compilation options
         -> Set Term -- ^ Public terms
         -> Set Term -- ^ Allowed message terms
         -> Int      -- ^ Maximum size of attacker knowledge
         -> LTS.Process
attacker opts@Options{..} public allowed k =
  LTS.Process "Attacker" Nothing False initialState body alphabet
  where (initialState, body) = serializeBody
                               $ makeBody (PQ.singleton 0 knw0) M.empty

        knw0 = knowledgeOfSet public

        -- Explore all knowledges that can be reached from the initial knowledge
        -- up to a given number of transitions, recording the transitions in the
        -- attacker body.
        makeBody :: PQueue Int Knowledge ->
                    -- Knowledges that still need to be visited, along with
                    -- their codes, ranked by their proximity from the initial
                    -- knowledge.
                    AttackerBody         ->
                    -- Body that has been built so far.
                    AttackerBody
        makeBody toVisit body =
          case PQ.minViewWithKey toVisit of
            Nothing -> body
            Just ((l, knw), toVisit')
              | M.member knw body -> makeBody toVisit' body
              | otherwise ->
                let transitions
                      | l == k    = []
                      | otherwise = [(m, updKnowledge m knw) | m <- S.toList allowed]

                    doKnowledge toVisit'' (_, knw')
                      | M.member knw' body = toVisit''
                      | otherwise          = PQ.insert (l + 1) knw' toVisit''

                    toVisit'' = foldl doKnowledge toVisit' transitions

                in makeBody toVisit'' (M.insert knw transitions body)

        -- Message relay transitions:
        -- send[HONEST][m:TERM] -> receive[HONEST][m] -> s
        relay :: LTS.Name -> LTS.Action
        relay s = LTS.straight [sendL    [LTS.Anon "HONEST", LTS.Binder "t" "TERM"],
                                receiveL [LTS.Anon "HONEST", LTS.Variable "t"]] s

        -- Message dropping transitions; no effect on the knowledge
        -- send[HONEST][TERM] -> s
        drop :: LTS.Name -> LTS.Action
        drop s = LTS.straight [sendL [LTS.Anon "HONEST", LTS.Anon "TERM"]] s

        -- When an agent sends a message to the network, the attacker can add it
        -- to his knowledge:
        --
        -- send[HONEST][m:TERM] -> updKnowledge m knw
        send :: [(Term, LTS.Name)] -> [LTS.Action]
        send next =
          [ LTS.Action (sendL $ [LTS.Anon "HONEST"] ++ labelOfTerm opts m mi) (LTS.Name knwi)
          | (mi, (m, knwi)) <- zip [0::Int ..] next]

        -- The attacker can send any message that it knows to an honest agent
        -- (i.e., the agent can receive anything the attacker knows).  This does
        -- not affect the attacker's knowledge.
        --
        -- when knows m knw, receive[HONEST][m:TERM] -> knw
        receive :: Knowledge -> LTS.Name -> [LTS.Action]
        receive knw knwi =
          let mis = [ LTS.Label $ labelOfTerm opts m mi
                    | (mi, m) <- zip [0::Int ..] (S.toList allowed)
                    , knows m knw ]in
            if null mis then []
            else [LTS.Action
                  (receiveL [LTS.Anon "HONEST", LTS.Set mis])
                  (LTS.Name knwi)]

        -- Describe all the transitions that are possible from the current state
        -- assuming that we know the LTS names of all the states that the
        -- attacker can transition to after observing a message.
        serializeState :: Knowledge -> LTS.Name -> [(Term, LTS.Name)] -> LTS.Body
        serializeState knw knwi next =
          LTS.Body $ [relay knwi] ++ [drop knwi] ++ send next ++ receive knw knwi

        -- Serialize the body of the attacker as an automaton by assigning
        -- indices to each possible knowledge.
        serializeBody :: AttackerBody ->
                         (LTS.Body, Map String (Maybe String, LTS.Body))
        serializeBody body =
          let name knw = "Q" ++ show (M.findIndex knw body)
              serialize (knw, next) =
                let knwi = name knw
                    ann | oPrintKnowledge = Just $ show $ pretty $ knw
                        | otherwise       = Nothing
                    serializeTransition (m, knw') = (m, LTS.Id $ name knw')
                    serializedTransitions = fmap serializeTransition next
                    st = serializeState knw (LTS.Id knwi) serializedTransitions
                in (knwi, (ann, st))
              body' = M.fromList $ map serialize $ M.assocs body
          in (LTS.Name (LTS.Id (name knw0)), body')

        alphabet = [ receiveL [LTS.Anon "HONEST", LTS.Anon "TERM"]
                   , sendL [LTS.Anon "HONEST", LTS.Anon "TERM"] ]

-- | Name of the automaton implementing an agent's thread.
threadName :: Agent -> Int -> String
threadName a id = "Def_Agent_" ++ agentName a ++ "_" ++ show id

-- | Package a thread's automaton body as a complete automaton.
compileThread :: M.Map Agent (S.Set Term)
                 -- Terms the agent can store
              -> S.Set Term
                 -- Allowed message terms
              -> [EventId]
                 -- Events the agent can trigger
              -> Agent
                 -- Agent identifier
              -> Int
                 -- Thread identifier
              -> LTS.Body
                 -- Thread body
              -> LTS.Process
compileThread stores allowed queries a id body =
  LTS.Process { pName = threadName a id
              , pParam = Nothing
              , pProperty = False
              , pBody = body
              , pDefs = M.empty
              , pAlphabet =
                [ sendL [agentLabel a, LTS.const id, LTS.Anon "TERM"]
                , receiveL [agentLabel a, LTS.const id, LTS.Anon "TERM"] ] ++
                [ beginL q [agentLabel a, LTS.const id, LTS.Anon "EVENT"]
                | q <- queries ] ++
                [ endL q [agentLabel a, LTS.const id, LTS.Anon "EVENT"]
                | q <- queries ] ++
                storeAlphabet a stores allowed id
              }

-- | Package the bodies of an agent's thread as a complete automaton.
compileAgent :: M.Map Agent (S.Set Term)
                -- Terms the agent can store
             -> S.Set Term
                -- Allowed Message Terms
             -> [EventId]
                -- Events the agent can trigger
             -> Agent
                -- Agent identifier
             -> [LTS.Body]
                -- Agent thread bodies
             -> (LTS.Parallel, [LTS.Process])
compileAgent stores allowed queries a bodies =
  let doThread = compileThread stores allowed queries a
      threads  = zipWith doThread [0 ..] bodies
      compose  = LTS.Parallel (agentName a)
                 $ LTS.Primitive $ map LTS.pName threads
  in (compose, threads)

-- | Compile a query to an automaton
compileQuery :: Map Agent Int -> EventId -> Query -> LTS.Process
compileQuery nSessions id Query{..} =
  let beginRange = LTS.Range 0 $ nSessions M.! qBegin - 1
      endRange   = LTS.Range 0 $ nSessions M.! qEnd   - 1

      begin  = LTS.Label [ LTS.Simple "begin"
                         , LTS.Simple id
                         , agentLabel qBegin
                         , beginRange
                         , LTS.Variable "E" ]
      end    = LTS.Label [ LTS.Simple "end"
                         , LTS.Simple id
                         , agentLabel qEnd
                         , endRange
                         , LTS.Variable "E" ]
      go l s = LTS.Action l $ LTS.Name $ LTS.Id s

      defs NonInjective =
        let body = LTS.Body [go begin "Q1", go end "Q1"]
        in M.singleton "Q1" (Nothing, body)

      defs Injective =
        let body = LTS.Body [LTS.straight [end] $ LTS.STOP Nothing]
        in M.singleton "Q1" (Nothing, body)

 in LTS.Process { pName = "Def_Query_" ++ id
                , pParam = Just "E"
                , pProperty = True
                , pBody = LTS.Body [go begin "Q1"]
                , pDefs = defs qProp
                , pAlphabet = [begin, end] }

-- | Range containing all the honest agents
honestRange :: Map Agent Int -> Doc ann
honestRange agents =
  braces $ cat $ punctuate comma
  $ [pretty (agentLabel a) <> dot <> brackets (pretty $ "0.." ++ show (i-1))
    |(a, i) <- M.assocs agents]

-- | Generate an automaton that implements the local storage for an agent
makeStore :: Set Term -- ^ Allowed messages in the network
          -> Set Term -- ^ Terms that can be stored by the agent
          -> Agent    -- ^ Agent identifier
          -> Int      -- ^ Number of threads the agent runs
          -> LTS.Process
makeStore allowed records a sessions =
  LTS.Process ("Store_" ++ agentName a) Nothing False initialState body alphabet
  where 
    combinations :: Int -> [a] -> [[a]]
    combinations 0 _ = [[]]
    combinations n xs = [y : ys | y:xs' <- tails xs, ys <- combinations (n - 1) xs']
    
    allComb :: Ord a => [a] -> [S.Set a]
    allComb l = map S.fromList $ concat result
      where len = length l
            result = map (`combinations`  l) [0.. len]

    -- turn off for now to keep the generated model the same as in the paper
    -- allComb :: Ord a => [a] -> [S.Set a]
    -- allComb = S.toList . S.powerSet . S.fromList 

    entries :: [S.Set Term]
    entries = allComb $ S.toList records

    name :: String
    name = map toLower $ agentName a

    range :: [Int]
    range = [0..sessions-1]

    tableBody :: M.Map (S.Set Term) Int
    tableBody = M.fromList $ zip entries [0..]
  
    stateLookup :: S.Set Term -> LTS.Body
    stateLookup entry = LTS.Name (LTS.Id $ stateLookup' entry)

    stateLookup' :: S.Set Term -> String
    stateLookup' entry = "Q" ++ (show (tableBody M.! entry))

    initialState = stateLookup []

    serializeRecords :: Term -> Int
    serializeRecords r = S.findIndex r allowed 

    oneState :: S.Set Term -> [Int] -> [LTS.Action]
    oneState s ns =
      actionF ++ (actionT <$> S.toList rest)
      where rest = S.difference records s
            ss = [LTS.Label [LTS.Variable (show x)] | x <- ns]
            fs = [LTS.Label [LTS.Variable (show (serializeRecords x))] | x <- S.toList s]
            insertT m = insertFreshL $ [LTS.Simple name,
                                        LTS.Set ss,
                                        LTS.Variable (show (serializeRecords m)),
                                        LTS.Simple "true"] 
            insertF = [LTS.Action (insertFreshL $ [LTS.Simple name,
                                                   LTS.Set ss,
                                                   LTS.Set fs,
                                                   LTS.Simple "false"])
                        (stateLookup s)] 
            actionT m = LTS.Action (insertT m) (stateLookup (s `S.union` (S.singleton m)))
            actionF = if S.null s then [] else insertF

    makeBody :: [S.Set Term] -> [Int] -> [(String, (Maybe String, LTS.Body))]
    makeBody [] _ = []
    makeBody (x:xs) ns = (stateLookup' x, (Nothing, LTS.Body (oneState x ns))) : makeBody xs ns
    
    body = M.fromList $ makeBody entries range

    alphabet =
      [ insertFreshL
        [ LTS.Simple name
        , LTS.Variable (show n)
        , LTS.Variable (show (serializeRecords m))
        , LTS.Simple r
        ]
      | n <- range
      , m <- S.toList records
      , r <- ["true", "false"]
      ]

-- | Number of threads declared for an agent
numInstance :: Agent -> M.Map Agent [LTS.Body] -> Int
numInstance a procs =
  case M.lookup a procs of
    Just l -> length l
    Nothing -> error $ "Making storage for undeclared agent" ++ agentName a

-- | Compute the alphabet used by the storage automaton.
storeAlphabet :: Agent
                 -- ^ Agent identifier
              -> M.Map Agent (S.Set Term)
                 -- ^ Terms that each agent can store
              -> S.Set Term
                 -- ^ Allowed messages in the network
              -> Int
                 -- ^ Thread identifier
              -> [LTS.Label]
storeAlphabet a nameToRecords allowed n =
  case M.lookup a nameToRecords of
    Just records ->
      let name = map toLower $ agentName a
       in [ insertFreshL
            [ LTS.Simple name
            , LTS.Variable (show n)
            , LTS.Variable (show (S.findIndex m allowed))
            , LTS.Simple result
            ]
          | m <- S.toList records
          , result <- ["true", "false"]
          ]
    Nothing -> []

-- | Compile a model given some options
compileWith :: Options   -- ^ Compilation options
            -> System () -- ^ Model description
            -> IO ()
compileWith opts@Options{..} sys =
  let Program {..}    = runSystem opts sys
      nSessions       = M.map length pProcs
      compiledAgents  = M.mapWithKey (compileAgent pStore pAllowed $ M.keys pQueries) pProcs
      compiledQueries = M.mapWithKey (compileQuery nSessions) pQueries
      doOutput h = do
        hPutStrLn h "// Ranges"
        if oVerboseMessages then do
          hPutStr h "set TERM = "
          hPrint h $ braces $ cat $ punctuate comma
            $ map (pretty . LTS.Label . labelOfTerm') $ S.toList pAllowed
        else do
          hPutStrLn h $ "range TERM = 0.." ++ show (S.size pAllowed - 1)
          when oPrintHeaders $ do
            hPutStrLn h "/* Term codes:"
            forM_ (zip [0 :: Int ..] $ S.toList pAllowed) $ \(i, m) -> do
              hPrint h $ pretty i <+> align (pretty m)
            hPutStrLn h "*/"
        if oVerboseMessages then do
          hPutStr h "set EVENT = "
          hPrint h $ braces $ cat $ punctuate comma
            $ map (pretty . LTS.Label . labelOfTerm') $ S.toList pEvents
        else do
          hPutStrLn h $ "range EVENT = 0.." ++ show (S.size pEvents - 1)
          when oPrintHeaders $ do
            hPutStrLn h "/* Event codes:"
            forM_ (zip [0 :: Int ..] $ S.toList pEvents) $ \(i, m) -> do
              hPrint h $ pretty i <+> align (pretty m)
            hPutStrLn h "*/"
        hPutStr h $ "set HONEST = "
        hPrint h $ honestRange nSessions
        hPutStrLn h "// Honest agents"
        forM_ compiledAgents $ \(def, threads) -> do
          forM_ threads (hPrint h . pretty)
          hPrint h $ pretty def
        hPutStrLn h "// Attacker"
        hPrint h $ pretty $ attacker opts pPublic pAllowed pKnowledgeSize
        hPutStrLn h "// Storages"
        forM_ (M.toList pStore) (\(name, records)-> hPrint h $ pretty $ makeStore pAllowed records name (numInstance name pProcs)) 
        let storesNames = map (("Store_" ++) . agentName) (M.keys pStore)
        let agentsNames = map (LTS.name . fst) (M.elems compiledAgents)
        hPrint h $ pretty $ LTS.Parallel "System" $ LTS.Primitive $ ("Attacker" : agentsNames) ++ storesNames
        hPutStrLn h "// Properties"
        forM_ (M.assocs compiledQueries) $ \(i, q) -> do
          let name = "Query_" ++ i
          hPrint h . pretty $ q
          hPrint h . pretty . LTS.Parallel name . LTS.Forall "e" "EVENT" . LTS.pName $ q
          hPrint h . pretty . LTS.Parallel ("Check_" ++ i) . LTS.Primitive $ ["System", name] in
  maybe (doOutput stdout) (\f -> withFile f WriteMode doOutput) oOutputFile

-- | Compile a model using the default options
compile :: System () -> IO ()
compile = compileWith defaultOptions
