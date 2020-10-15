{-# LANGUAGE DeriveFunctor #-}

{-|

This module defines the syntax of LTSA automata.

-}

module Taglierino.LTS where

import Data.Text.Prettyprint.Doc
import qualified Data.Map.Strict as M

class HasName a where
  name :: a -> String

data Name = Id String
          | STOP (Maybe String)
          | ERROR
  deriving (Eq, Ord)

comment :: String -> Doc ann
comment = enclose (space <> pretty "/* ") (pretty " */" <> space) . pretty

instance Pretty Name where
  pretty (Id x) = pretty x
  pretty (STOP Nothing) = pretty "STOP"
  pretty (STOP (Just info)) = pretty "STOP" <+> comment info
  pretty ERROR = pretty "ERROR"

type Type     = String
type Variable = String

data Const = Const Int (Maybe String)
  deriving (Eq, Ord)

instance Pretty Const where
  pretty (Const i Nothing)  = brackets (pretty i)
  pretty (Const i (Just x)) = brackets (pretty i <> comment x)

data LabelPart = Simple   String
               | Binder   Variable String
               | Variable Variable
               | Anon     Type
               | Set      [Label]
               | Range    Int Int
               | Int      Const
  deriving (Eq, Ord)

instance Pretty LabelPart where
  pretty (Simple l)    = pretty l
  pretty (Binder x ty) = brackets (pretty x <> colon <> pretty ty)
  pretty (Variable x)  = brackets (pretty x)
  pretty (Anon ty)     = brackets (pretty ty)
  pretty (Set ls)      = braces $ cat $ punctuate comma $ map pretty ls
  pretty (Range lb ub) = brackets (pretty lb <> pretty ".." <> pretty ub)
  pretty (Int i)       = pretty i

consts :: [Const] -> LabelPart
consts is = Set [Label [Int i] | i <- is]

const :: Int -> LabelPart
const i = Int $ Const i Nothing

data Label = Label [LabelPart]
  deriving (Eq, Ord)

instance Pretty Label where
  pretty (Label parts) = concatWith (surround dot) $ map pretty parts

data Action = Action Label Body
  deriving (Eq, Ord)

instance Pretty Action where
  pretty (Action x b) = pretty x <+> pretty "->" <+> pretty b

data Body = Body [Action]
          | Name Name
  deriving (Eq, Ord)

prettyBody :: Bool -> Body -> Doc ann
prettyBody _ (Body []) = pretty "STOP"
prettyBody topLevel (Body [choice])
  | topLevel  = parens $ pretty choice
  | otherwise = pretty choice
prettyBody _ (Body choices) =
  parens $ sep $ punctuate (pretty "|") $ map pretty choices
prettyBody _ (Name n) = pretty n

instance Pretty Body where
  pretty = prettyBody False

data Process = Process { pName :: String
                       , pParam :: Maybe String
                       , pProperty :: Bool
                       , pBody :: Body
                       , pDefs :: M.Map String (Maybe String, Body)
                       , pAlphabet :: [Label] }
  deriving (Eq, Ord)

instance HasName Process where
  name = pName

instance Pretty Process where
  pretty (Process name param prop body defs alphabet) =
    vcat [header,
          if length alphabet == 0 then dot
          else pretty "+" <+> actions <> dot]
    where header
            | prop      = pretty "property" <+> declaration
            | otherwise = declaration
          paramList Nothing  = mempty
          paramList (Just x) = parens (pretty x <> pretty "=0")
          declaration = pretty name <> paramList param <+> pretty "=" <+> prettyBody True body <+> localDefs
          localDefs
            | M.null defs = mempty
            | otherwise = comma <> line <> (vcat $ punctuate comma $ map doState $ M.assocs defs)
          actions = braces $ cat $ punctuate comma $ map pretty alphabet

          showInfo Nothing     = mempty
          showInfo (Just info) = comment info

          doState (x, (info, b)) =
              pretty x <+> showInfo info <> pretty "=" <+> prettyBody True b

straight :: [Label] -> Name -> Action
straight [] _ = error "Cannot build an empty action"
straight (l : ls) n = Action l $ straightBody ls n

straightBody :: [Label] -> Name -> Body
straightBody [] n = Name n
straightBody (l : ls) n = Body [Action l $ straightBody ls n]

data ParallelBody = Primitive [String]
                  | Forall Variable Type String
  deriving (Eq, Ord, Show)

instance Pretty ParallelBody where
  pretty (Primitive names) =
    parens $ concatWith (surround $ pretty "||") $ map pretty names
  pretty (Forall x ty name) =
    pretty "forall" <> brackets (pretty x <> colon <> pretty ty) <+>
    pretty name <> parens (pretty x)

data Parallel = Parallel String ParallelBody
  deriving (Eq, Ord, Show)

instance HasName Parallel where
  name (Parallel x _) = x

instance Pretty Parallel where
  pretty (Parallel name body) =
    pretty "||" <+> pretty name <+> pretty "=" <+>
    pretty body <> dot
