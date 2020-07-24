{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists, ExtendedDefaultRules #-}

module Taglierino where

import qualified Taglierino.LTS as LTS

import Prelude hiding (fail)
import qualified Prelude

import Data.Foldable
import Data.Char
import Data.List (intersperse)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.MultiSet as MS
import Data.Text.Prettyprint.Doc
import qualified Data.Dequeue as Q
import qualified Data.PQueue.Prio.Min as PQ
import Data.Maybe (isJust)

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

data Options = Options { oPrintHeaders    :: Bool
                       , oPrintErrors     :: Bool
                       , oPrintMessages   :: Bool
                       , oPrintKnowledge  :: Bool
                       , oVerboseMessages :: Bool }
  deriving (Eq, Ord, Show)

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
          | Xor (Set Term)
          | AEAD Term Term Term Term
          | Garbage
  deriving (Eq, Ord, Show)

labelOfId :: Id -> [LTS.LabelPart]
labelOfId (Id Nothing i)  = [LTS.const i]
labelOfId (Id (Just a) i) = [agentLabel a, LTS.const i]

labelOfKeyType :: KeyType -> [LTS.LabelPart]
labelOfKeyType Private = [LTS.Simple "priv"]
labelOfKeyType Public  = [LTS.Simple "pub"]

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
        go (Xor ts)   = [LTS.Simple "xor"]
                        ++ concat (intersperse [LTS.Simple "comma"] $ map go $ S.toList ts)
                        ++ [LTS.Simple "dot"]
        go (AEAD t1 t2 t3 t4) = [LTS.Simple "aead"]
                                ++ concat (intersperse [LTS.Simple "comma"] $ map go [t1, t2, t3, t4])
                                ++ [LTS.Simple "dot"]
        go Garbage = [LTS.Simple "g"]

labelOfTerm :: Options -> Term -> Int -> [LTS.LabelPart]
labelOfTerm opts t ti
  | oVerboseMessages opts = labelOfTerm' t
  | oPrintMessages opts   = [LTS.Int $ LTS.Const ti $ Just $ show $ pretty t]
  | otherwise             = [LTS.const ti]

prettyTerm :: Pretty a => Int -> a -> Doc ann
prettyTerm 1 x = pretty x
prettyTerm i x = pretty i <+> pretty "*" <+> pretty x

occurrences :: (Ord a) => MS.MultiSet a -> [(a, Int)]
occurrences ms =
  [(x, MS.occur x ms) | x <- MS.distinctElems ms]

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
  ["Def_", "Check_"]

mkAgent :: String -> Agent
mkAgent [] = error "Agent name cannot be empty"
mkAgent a@(c : s)
  | not $ isAsciiUpper c =
    error $ "Agent name begin with an upper-case letter (given " ++ a ++ ")"
  | not $ all (\c' -> isAscii c' && isAlphaNum c') s =
    error $ "Agent name must only have alphanumeric characters (given " ++ a ++ ")"
  | a `elem` reservedNames =
    error $ "The identifier \"" ++ a ++ "\" is reserved"
  | otherwise =
    Agent a

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
  pretty (Xor ms) =
    encloseSep (pretty "(") (pretty ")") (pretty "(+)") $ map pretty $ S.toList ms
  pretty (AEAD m1 m2 m3 m4) = pretty "AEAD" <> pretty (Tup [m1, m2, m3, m4])
  pretty Garbage = pretty "Garbage"

instance Exts.IsList Term where
  type Item Term = Term
  fromList = Tup
  toList (Tup xs) = xs
  toList m = fail $ "Not a tuple: " ++ show (pretty m)

class NewNonce m where
  newNonce :: m Term

class NewConst m where
  newConst :: m Term

class NewAKey m where
  newAKey :: m Term

class NewSKey m where
  newSKey :: m Term

class NewSigKey m where
  newSigKey :: m Term

class MonadOptions m where
  options :: m Options

data ProcRState = ProcRState { psAllowed :: S.Set Term
                             , psEvents  :: S.Set Term
                             , psAgent   :: Agent
                             , psThread  :: Int
                             , psOptions :: Options }
  deriving (Eq, Ord)

data ProcState = ProcState { psNonces  :: Int
                           , psAKeys   :: Int
                           , psSKeys   :: Int
                           , psSigKeys :: Int
                           , psConsts  :: Int }
  deriving (Eq, Ord)

newtype Proc a =
  Proc { unProc :: ContT LTS.Body
                   (ReaderT ProcRState
                    (State ProcState)) a }

deriving instance Functor Proc
deriving instance Applicative Proc
deriving instance Monad Proc
deriving instance MonadReader ProcRState Proc
deriving instance MonadState ProcState Proc

instance MonadOptions Proc where
  options = do
    ProcRState{..} <- ask
    return psOptions

instance MonadFail Proc where
  fail m = do
    printErrors <- oPrintErrors <$> options
    let ann = if printErrors then Just m else Nothing
    Proc $ ContT $ \_ -> return $ LTS.Name $ LTS.STOP ann

throwError :: Proc ()
throwError = Proc $ mapContT (\_ -> return $ LTS.Name LTS.ERROR) $ return ()

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

action :: LTS.Label -> Proc ()
action l = Proc $ mapContT (\k -> (\res -> LTS.Body [LTS.Action l res]) <$> k) $ return ()

sendL :: [LTS.LabelPart] -> LTS.Label
sendL args = LTS.Label $ [LTS.Simple "send"] ++ args

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

begin :: EventId -> Term -> Proc ()
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

end :: EventId -> Term -> Proc ()
end e m = do
  ProcRState{..} <- ask
  case S.lookupIndex m psEvents of
    Just mi ->
      action $ endL e $ [agentLabel psAgent, LTS.const psThread]
      ++ labelOfTerm psOptions m mi
    Nothing -> fail $ show $ pretty "Not allowed to emit" <+> pretty m

receiveL :: [LTS.LabelPart] -> LTS.Label
receiveL args = LTS.Label $ [LTS.Simple "receive"] ++ args

receive :: Proc Term
receive = do
  ProcRState{..} <- ask
  Proc $ ContT $ \k -> do
    s <- get
    actions <- forM (zip [0 ..] $ S.toList psAllowed) $ \(mi, m) -> do
      put s
      body <- k m
      let l = receiveL $ [agentLabel psAgent, LTS.const psThread]
              ++ labelOfTerm psOptions m mi
      return $ LTS.Action l body
    return $ LTS.Body actions

aenc :: Term -> Term -> Term
aenc (AKey k Public) m = AEnc k m
aenc _ _ = Garbage

decodeFail :: Term -> Term -> Proc a
decodeFail m1 m2 =
  fail $ show $ pretty "Decoding failed:" <+> pretty m1 <+> pretty m2

checkSignFail :: Term -> Term -> Proc a
checkSignFail m1 m2 =
  fail $ show $ pretty "check signature failed:" <+> pretty m1 <+> pretty m2

adec :: Term -> Term -> Proc Term
adec m1@(AKey k1 Private) m2@(AEnc k2 m) =
  if k1 == k2 then return m
  else decodeFail m1 m2
adec m1 m2 = decodeFail m1 m2

senc :: Term -> Term -> Term
senc (SKey k) m = SEnc k m
senc _ _ = Garbage

sdec :: Term -> Term -> Proc Term
sdec m1@(SKey k1) m2@(SEnc k2 m) =
  if k1 == k2 then return m
  else decodeFail m1 m2
sdec m1 m2 = decodeFail m1 m2

sign :: Term -> Term -> Term
sign (SigKey k Private) m = Sign k m
sign _ _ = Garbage

pkey :: Term -> Term
pkey (SigKey k Private) = SigKey k Public
pkey (AKey k Private)   = AKey k Public
pkey m = error $ "Not a private key: " ++ show (pretty m)

checkSig :: Term -> Term -> Term -> Proc Bool
checkSig (SigKey k1 Public) (Sign k2 m2) m3 =
  return (k1 == k2 && m2 == m3)
checkSig _ _ _ = return False

checkSign :: Term -> Term -> Proc Term
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

xorSet :: S.Set Term -> Term
xorSet ms
  | S.size ms == 1 = S.findMin ms
  | otherwise      = Xor ms

xor :: Term -> Term -> Term
xor (Xor ms1) (Xor ms2) =
  let u   = S.union ms1 ms2
      i   = S.intersection ms1 ms2 in
    xorSet $ S.difference u i
xor (Xor ms1) m2
  | S.member m2 ms1 = xorSet $ S.delete m2 ms1
  | otherwise       = xorSet $ S.insert m2 ms1
xor m1 (Xor ms2)
  | S.member m1 ms2 = xorSet $ S.delete m1 ms2
  | otherwise       = xorSet $ S.insert m1 ms2
xor m1 m2
  | m1 == m2  = Xor S.empty
  | otherwise = Xor $ S.fromList [m1, m2]

inc :: Term -> Term
inc = Hash

aead_enc :: Term -> Term -> Term -> Term -> Term
aead_enc m1 m2 m3 m4 = AEAD m1 m2 m3 m4

aead_dec :: Term -> Term -> Term -> Term -> Proc Term
aead_dec m1 m2 m3@(AEAD m1' m2' m3' m4') m4 =
  if (m1==m1' && m2 == m2'&& m4 == m4') then return m3'
  else decodeFail m1 m3
aead_dec m1 _ m3 _  = decodeFail m1 m3

tup :: [Term] -> Term
tup = Tup

untup :: (Monad m, MonadFail m) => Term -> m [Term]
untup (Tup ms) = return ms
untup m = fail $ show $ pretty "Not a tuple:" <+> pretty m

runProc :: Proc () -> S.Set Term -> S.Set Term -> Agent -> Int -> Options -> LTS.Body
runProc (Proc f) psAllowed psEvents psAgent psThread psOptions =
  fst (runState (runReaderT (runContT f (\() -> return $ LTS.Name $ LTS.STOP Nothing)) ProcRState{..}) $ ProcState 0 0 0 0 0)

data Query = NonInjective | Injective
  deriving (Eq, Ord)

data SystemState = SystemState { sAgents :: Int
                               , sNonces :: Int
                               , sAKeys  :: Int
                               , sSKeys  :: Int
                               , sSigKeys :: Int
                               , sConsts :: Int
                               , sEvents  :: S.Set Term
                               , sAllowed :: S.Set Term
                               , sPublic  :: S.Set Term
                               , sKnowledgeSize :: Int
                               , sOptions :: Options
                               , sProcs   :: M.Map Agent (Queue (Proc ()))
                               , sQueries :: Map EventId Query }

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

events :: [Term] -> System ()
events evs = do
  SystemState {..} <- get
  put $ SystemState {sEvents = sEvents `S.union` S.fromList evs, ..}

query :: EventId -> Query -> System ()
query id q = do
  SystemState {..} <- get
  put $ SystemState {sQueries = M.insert id q sQueries, ..}

nonInjective :: EventId -> System ()
nonInjective = flip query NonInjective

injective :: EventId -> System ()
injective = flip query Injective

allow :: [Term] -> System ()
allow ms = do
  SystemState {..} <- get
  put $ SystemState {sAllowed = sAllowed `S.union` S.fromList ms, ..}

public :: [Term] -> System ()
public iks = do
  SystemState {..} <- get
  put $ SystemState {sPublic = sPublic `S.union` S.fromList iks, ..}

knowledgeSize :: Int -> System ()
knowledgeSize k = do
  SystemState{..} <- get
  put $ SystemState{sKnowledgeSize = k, ..}

agent :: String -> Proc () -> System ()
agent a p = do
  SystemState {..} <- get
  let a' = mkAgent a
  let q  = M.findWithDefault Q.empty a' sProcs
  put $ SystemState {sProcs = M.insert a' (Q.pushBack q p) sProcs, ..}

data Program =
  Program { pEvents        :: S.Set Term
          , pAllowed       :: S.Set Term
          , pPublic        :: S.Set Term
          , pKnowledgeSize :: Int
          , pQueries       :: Map EventId Query
          , pProcs         :: M.Map Agent [LTS.Body] }

runSystem :: Options -> System () -> Program
runSystem opts (System f) =
  let initialState = SystemState { sAgents = 0
                                 , sNonces = 0
                                 , sAKeys  = 0
                                 , sSKeys  = 0
                                 , sSigKeys = 0
                                 , sConsts = 0
                                 , sEvents  = S.empty
                                 , sAllowed = S.empty
                                 , sPublic  = S.empty
                                 , sKnowledgeSize = 0
                                 , sOptions = opts
                                 , sProcs   = M.empty
                                 , sQueries = M.empty }
      ((), SystemState {..}) = runState f initialState
      run a id p = runProc p sAllowed sEvents a id opts
      procs = M.mapWithKey (\a ps -> zipWith (run a) [0 ..] $ toList ps) sProcs in
    Program sEvents sAllowed sPublic sKnowledgeSize sQueries procs

-- | Elementary messages are those that cannot be further decomposed by the
-- attacker.  Once the attacker knows an elementary message, we can keep this
-- message in the knowledge set, whereas other messages can be further analyzed
-- to extract more knowledge.

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
elementary (Xor _)         = False
elementary (AEAD _ _ _ _)  = False
elementary Garbage         = False

-- | Set of messages known by the attacker.  As an optimization, we ensure that
-- this set never contains a tuple, since knowing a tuple is equivalent to
-- knowing its components.
data Knowledge = Knowledge { kPerm :: S.Set Term, kTemp :: S.Set Term }
  deriving (Eq, Ord)

instance Pretty Knowledge where
  pretty Knowledge{..} = pretty $ (S.toList kPerm, S.toList kTemp)

kempty :: Knowledge
kempty = Knowledge S.empty S.empty

kunion :: Knowledge -> Knowledge -> Knowledge
kunion (Knowledge pk1 tk1) (Knowledge pk2 tk2) =
  Knowledge (S.union pk1 pk2) (S.union tk1 tk2)

kinsert :: Term -> Knowledge -> Knowledge
kinsert m Knowledge{..}
  | elementary m = Knowledge { kPerm = S.insert m kPerm, .. }
  | otherwise    = Knowledge { kTemp = S.insert m kTemp, .. }

kremove :: Term -> Knowledge -> Knowledge
kremove m knw@Knowledge{..}
  | elementary m = knw
  | otherwise    = Knowledge kPerm (S.delete m kTemp)

ksingleton :: Term -> Knowledge
ksingleton m = kinsert m kempty

kmember :: Term -> Knowledge -> Bool
kmember m Knowledge{..}
  | elementary m = S.member m kPerm
  | otherwise    = S.member m kTemp

-- | Attempt to factor a multiset as a union of multisets by doing a graph search.

factorMultiSet :: Ord a =>
                  [MS.MultiSet a] -> -- ^ Allowed factors
                  MS.MultiSet a   -> -- ^ Multiset to be factored
                  Maybe [Int]     -- ^ Coefficients for each multiset
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
knows (Xor ms) knw =
  -- TODO: This check is very incomplete.  We would need to solve a linear
  -- system to make this work in full generality
  -- TODO: What if ms' is a singleton?
  let ms' = S.filter (\m -> not $ knows m knw) ms in
    length ms' == 0 || kmember (Xor ms') knw
knows (AEAD m1 m2 m3 m4) knw =
  -- TODO: Can we simplify this?
  kmember (AEAD m1 m2 m3 m4) knw
  || all (flip knows knw) [m1, m2, m3, m4]
knows Garbage _ = False

knull :: Knowledge -> Bool
knull Knowledge{..} = S.null kPerm && S.null kTemp

ksub :: Knowledge -> Knowledge -> Bool
ksub knw1 knw2 =
  all (flip knows knw2) (kPerm knw1) &&
  all (flip knows knw2) (kTemp knw1)

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
extractKnowledge m@(Xor _) knw = extractKnowledge1 m knw -- TODO: Incomplete
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
      init           = (Knowledge (kPerm knw) S.empty, False)
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
  let (kPerm, kTemp) = S.partition elementary ms in
    knormalize Knowledge{..}

type AttackerBody = M.Map Knowledge [(Term, Knowledge)]

attacker :: Options -> Set Term -> Set Term -> Int -> LTS.Process
attacker opts@Options{..} public allowed k =
  LTS.Process "Attacker" Nothing False initialState body alphabet
  where (initialState, body) = makeBody (PQ.singleton 0 knw0) M.empty

        knw0 = knowledgeOfSet public

        makeBody :: PQueue Int Knowledge -> AttackerBody -> (LTS.Body, Map String (Maybe String, LTS.Body))
        makeBody toVisit body =
          case PQ.minViewWithKey toVisit of
            Nothing ->
              serializeBody body
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

        -- receive[HONEST][m:TERM] -> send[HONEST][m] -> s
        relay :: LTS.Name -> LTS.Action
        relay s = LTS.straight [sendL    [LTS.Anon "HONEST", LTS.Binder "t" "TERM"],
                                receiveL [LTS.Anon "HONEST", LTS.Variable "t"]] s

        -- receive[HONEST][TERM] -> s
        drop :: LTS.Name -> LTS.Action
        drop s = LTS.straight [sendL [LTS.Anon "HONEST", LTS.Anon "TERM"]] s

        -- send[HONEST][m:TERM] -> updKnowledge m knw
        send :: [(Term, LTS.Name)] -> [LTS.Action]
        send next =
          [ LTS.Action (sendL $ [LTS.Anon "HONEST"] ++ labelOfTerm opts m mi) (LTS.Name knwi)
          | (mi, (m, knwi)) <- zip [0::Int ..] next]

        -- when knows m knw, receive[HONEST][m:TERM] -> knw
        receive :: Knowledge -> LTS.Name -> [LTS.Action]
        receive knw knwi =
          let mis = [ LTS.Label $ labelOfTerm opts m mi
                    | (mi, m) <- zip [0::Int ..] (S.toList allowed)
                    , knows m knw ]in
            if null mis then []
            else [LTS.Action (receiveL [LTS.Anon "HONEST", LTS.Set mis]) (LTS.Name knwi)]

        serializeState :: Knowledge -> LTS.Name -> [(Term, LTS.Name)] -> LTS.Body
        serializeState knw knwi next =
          LTS.Body $ [relay knwi] ++ [drop knwi] ++ send next ++ receive knw knwi

        serializeBody :: AttackerBody -> (LTS.Body, Map String (Maybe String, LTS.Body))
        serializeBody body =
          let name knw = "Q" ++ show (M.findIndex knw body)
              body' = M.fromList [ (knwi,
                                    (ann,
                                     serializeState knw (LTS.Id knwi) (fmap (\(m, knw') -> (m, LTS.Id $ name knw')) next)))
                                 | (knw, next) <- M.assocs body
                                 , let knwi = name knw
                                 , let ann  = if oPrintKnowledge then Just (show $ pretty $ knw)
                                              else Nothing ]
          in (LTS.Name (LTS.Id (name knw0)), body')

        alphabet = [ receiveL [LTS.Anon "HONEST", LTS.Anon "TERM"]
                   , sendL [LTS.Anon "HONEST", LTS.Anon "TERM"] ]

threadName :: Agent -> Int -> String
threadName a id = "Def_Agent_" ++ agentName a ++ "_" ++ show id

compileThread :: [EventId] -> Agent -> Int -> LTS.Body -> LTS.Process
compileThread queries a id body =
  LTS.Process { pName = threadName a id
              , pParam = Nothing
              , pProperty = False
              , pBody = body
              , pDefs = M.empty
              , pAlphabet = [ sendL [agentLabel a, LTS.const id, LTS.Anon "TERM"]
                            , receiveL [agentLabel a, LTS.const id, LTS.Anon "TERM"] ] ++
                            [ beginL q [agentLabel a, LTS.const id, LTS.Anon "EVENT"]
                            | q <- queries ] ++
                            [ endL q [agentLabel a, LTS.const id, LTS.Anon "EVENT"]
                            | q <- queries ]
              }


compileAgent :: [EventId] -> Agent -> [LTS.Body] -> (LTS.Parallel, [LTS.Process])
compileAgent queries a bodies =
  let threads  = zipWith (compileThread queries a) [0 ..] bodies
      compose  = LTS.Parallel (agentName a) $ LTS.Primitive $ map LTS.pName threads in
    (compose, threads)

compileQuery :: EventId -> Query -> LTS.Process
compileQuery id q =
  let begin  = LTS.Label [ LTS.Simple "begin"
                         , LTS.Simple id
                         , LTS.Anon "HONEST"
                         , LTS.Variable "E" ]
      end    = LTS.Label [ LTS.Simple "end"
                         , LTS.Simple id
                         , LTS.Anon "HONEST"
                         , LTS.Variable "E" ]
      go l s = LTS.Action l $ LTS.Name $ LTS.Id s

      defs NonInjective =
        M.singleton "Q1" (Nothing, LTS.Body [go begin "Q1", go end "Q1"])

      defs Injective =
        M.singleton "Q1" (Nothing, LTS.Body [LTS.straight [end] $ LTS.STOP Nothing]) in

    LTS.Process { pName = "Def_Query_" ++ id
                , pParam = Just "E"
                , pProperty = True
                , pBody = LTS.Body [go begin "Q1"]
                , pDefs = defs q
                , pAlphabet = [begin, end] }

honestRange :: [(Agent, Int)] -> Doc ann
honestRange agents =
  braces $ cat $ punctuate comma
  $ [pretty (agentLabel a) <> dot <> brackets (pretty $ "0.." ++ show (i-1))
    |(a, i) <- agents]

compileWith :: Options -> System () -> IO ()
compileWith opts@Options{..} sys = do
  let Program {..}    = runSystem opts sys
  let compiledAgents  = M.mapWithKey (compileAgent $ M.keys pQueries) pProcs
  let compiledQueries = M.mapWithKey compileQuery pQueries
  putStrLn "// Ranges"
  if oVerboseMessages then do
    putStr "set TERM = "
    print $ braces $ cat $ punctuate comma
      $ map (pretty . LTS.Label . labelOfTerm') $ S.toList pAllowed
  else do
    putStrLn $ "range TERM = 0.." ++ show (S.size pAllowed - 1)
    when oPrintHeaders $ do
      putStrLn "/* Term codes:"
      forM_ (zip [0 :: Int ..] $ S.toList pAllowed) $ \(i, m) -> do
        print $ pretty i <+> align (pretty m)
      putStrLn "*/"
  if oVerboseMessages then do
    putStr "set EVENT = "
    print $ braces $ cat $ punctuate comma
      $ map (pretty . LTS.Label . labelOfTerm') $ S.toList pEvents
  else do
    putStrLn $ "range EVENT = 0.." ++ show (S.size pEvents - 1)
    when oPrintHeaders $ do
      putStrLn "/* Event codes:"
      forM_ (zip [0 :: Int ..] $ S.toList pEvents) $ \(i, m) -> do
        print $ pretty i <+> align (pretty m)
      putStrLn "*/"
  putStr $ "set HONEST = "
  print $ honestRange [(a, length ps) | (a, ps) <- M.assocs pProcs]
  putStrLn "// Honest agents"
  forM_ compiledAgents $ \(def, threads) -> do
    forM_ threads (print . pretty)
    print $ pretty def
  putStrLn "// Attacker"
  print $ pretty $ attacker opts pPublic pAllowed pKnowledgeSize
  print $ pretty $ LTS.Parallel "System" $ LTS.Primitive $ "Attacker" : map (LTS.name . fst) (M.elems compiledAgents)
  putStrLn "// Properties"
  forM_ (M.assocs compiledQueries) $ \(i, q) -> do
    let name = "Query_" ++ i
    print . pretty $ q
    print . pretty . LTS.Parallel name . LTS.Forall "e" "EVENT" . LTS.pName $ q
    print . pretty . LTS.Parallel ("Check_" ++ i) . LTS.Primitive $ ["System", name]

compile :: System () -> IO ()
compile = compileWith (Options False False False False False)
