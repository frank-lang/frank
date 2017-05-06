{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
-- The raw abstract syntax and (refined) abstract syntax for Frank
module Syntax where

import qualified Data.Map.Strict as M
import Data.List

import Data.IORef

import System.IO.Unsafe

import qualified Text.PrettyPrint as PP

{-------------------}
{-- Syntax description: raw syntax comes from the parser and preprocessed into
    refined syntax. --}

class NotRaw a where
  idNotRaw :: a -> a

class NotDesugared a where
  idNotDesugared :: a -> a

-- output from the parser
data Raw = MkRaw

instance NotDesugared Raw where
  idNotDesugared = Prelude.id

-- well-formed AST (after tidying up the output from the parser)
data Refined = MkRefined

instance NotDesugared Refined where
  idNotDesugared = Prelude.id

instance NotRaw Refined where
  idNotRaw = Prelude.id

-- desugaring of types:
--   * type variables are given unique names
--   * strings are lists of characters
data Desugared = MkDesugared

instance NotRaw Desugared where
  idNotRaw = Prelude.id

{-- The raw syntax as parsed in from the file and the refined syntax produced
    by a preprocessing stage before typechecking are simultaneously defined
    using GADT syntax. --}

data Prog a = MkProg [TopTm a]
            deriving (Show, Eq)

{---------------}
{- Parts of the grammar specific to the raw syntax. -}

-- A top-level multihandler signature and clause.
data MHSig = MkSig Id (CType Raw)
             deriving (Show, Eq)

data MHCls = MkMHCls Id (Clause Raw)
           deriving (Show, Eq)

{---------------}
{- Parts of the grammar specific to the refined syntax. -}

-- FIXME: currently all top-level bindings are mutually
-- recursive. This setup will break if we add non-recursive value
-- bindings.
--
-- An obvious design is to group mutually recursive bindings using
-- letrec, as specified in the paper.
--
-- Data and interface definitions can continue to be globally mutually
-- recursive as they do not depend on values.

-- a recursive multihandler definition
data MHDef a = MkDef Id (CType a) [Clause a]
           deriving (Show, Eq)

-- value bindings - not yet supported
-- data VDef a = VDef Id (VType a) (Tm a)

{- MH here = 'operator' in the paper. Operator here doesn't have a name
   in the paper. -}

data Operator = MkMono Id | MkPoly Id | MkCmdId Id
              deriving (Show, Eq)

data DataCon a = MkDataCon Id [Tm a]
               deriving (Show, Eq)

{---------------}
{- Parts of the grammar independent of the syntax. -}

-- A raw term collects multihandler signatures and clauses separately. A
-- refined top-level term collects multihandler signatures and clauses in one
-- definition.
data TopTm a where
  MkDataTm :: DataT a -> TopTm a
  MkItfTm :: Itf a -> TopTm a
  MkSigTm :: MHSig -> TopTm Raw
  MkClsTm :: MHCls -> TopTm Raw
  MkDefTm :: NotRaw a => MHDef a -> TopTm a

deriving instance (Show) (TopTm a)
deriving instance (Eq) (TopTm a)

data Use a where
  MkRawId :: Id -> Use Raw
  MkRawComb :: Use Raw -> [Tm Raw] -> Use Raw
  MkOp :: NotRaw a => Operator -> Use a
  MkApp :: NotRaw a => Use a -> [Tm a] -> Use a

deriving instance (Show) (Use a)
deriving instance (Eq) (Use a)

-- Tm here = 'construction' in the paper

data Tm a where
  MkSC :: SComp a -> Tm a
  MkLet :: Id -> Tm Raw -> Tm Raw -> Tm Raw
  MkStr :: String -> Tm a
  MkInt :: Integer -> Tm a
  MkChar :: Char -> Tm a
  MkList :: [Tm Raw] -> Tm Raw
  MkTmSeq :: Tm a -> Tm a -> Tm a
  MkUse :: Use a -> Tm a
  MkDCon :: NotRaw a => DataCon a -> Tm a

deriving instance (Show) (Tm a)
deriving instance (Eq) (Tm a)

-- A clause for a multihandler definition
data Clause a = MkCls [Pattern a] (Tm a)
  deriving (Show, Eq)

data SComp a = MkSComp [Clause a]
  deriving (Show, Eq)

data Kind = VT   -- value type
          | ET   -- effect type
  deriving (Show, Eq)

data DataT a = MkDT Id [(Id, Kind)] [Ctr a]
  deriving (Show, Eq)

data Itf a = MkItf Id [(Id, Kind)] [Cmd a]
  deriving (Show, Eq)

data Ctr a = MkCtr Id [VType a]
  deriving (Show, Eq)

data Cmd a = MkCmd Id [VType a] (VType a)
  deriving (Show, Eq)

data Pattern a where
  MkVPat :: ValuePat a -> Pattern a
  MkCmdPat :: Id -> [ValuePat a] -> Id -> Pattern a
  MkThkPat :: Id -> Pattern a
    deriving (Show, Eq)

-- TODO: should we compile away string patterns into list of char patterns?
data ValuePat a where
  MkVarPat :: Id -> ValuePat a
  MkDataPat :: Id -> [ValuePat a] -> ValuePat a
  MkIntPat :: Integer -> ValuePat a
  MkCharPat :: Char -> ValuePat a
  MkStrPat :: String -> ValuePat a
  MkConsPat :: ValuePat Raw -> ValuePat Raw -> ValuePat Raw
  MkListPat :: [ValuePat Raw] -> ValuePat Raw

deriving instance (Show) (ValuePat a)
deriving instance (Eq) (ValuePat a)

type Id = String

-- Type hierarchy
data CType a = MkCType [Port a] (Peg a)
  deriving (Show, Eq)

data Port a = MkPort (Adj a) (VType a)
  deriving (Show, Eq)

data Peg a = MkPeg (Ab a) (VType a)
  deriving (Show, Eq)

data VType a where
  MkDTTy :: Id -> [TyArg a] -> VType a
  MkSCTy :: CType a -> VType a
  MkTVar :: NotDesugared a => Id -> VType a
  MkRTVar :: Id -> VType Desugared
  MkFTVar :: Id -> VType Desugared
  MkStringTy :: NotDesugared a => VType a
  MkIntTy :: VType a
  MkCharTy :: VType a

deriving instance (Show) (VType a)
deriving instance (Eq) (VType a)

type ItfMap a = M.Map Id [TyArg a]

-- Adjustments
data Adj a = MkAdj (ItfMap a)
  deriving (Show, Eq)

-- Abilities
data Ab a = MkAb (AbMod a) (ItfMap a)
  deriving (Show, Eq)

data AbMod a where
  MkEmpAb :: AbMod a
  MkAbVar :: NotDesugared a => Id -> AbMod a
  MkAbRVar :: Id -> AbMod Desugared
  MkAbFVar :: Id -> AbMod Desugared

deriving instance Show (AbMod a)
deriving instance Eq (AbMod a)

data TyArg a where
  VArg :: VType a -> TyArg a
  EArg :: Ab a    -> TyArg a

deriving instance Show (TyArg a)
deriving instance Eq (TyArg a)

idAdj :: Adj a
idAdj = MkAdj M.empty

desugaredStrTy :: VType Desugared
desugaredStrTy = MkDTTy "List" [VArg MkCharTy]

getItfs :: [TopTm a] -> [Itf a]
getItfs xs = getItfs' xs []
  where getItfs' :: [TopTm a] -> [Itf a] -> [Itf a]
        getItfs' ((MkItfTm itf) : xs) ys = getItfs' xs (itf : ys)
        getItfs' (_ : xs) ys = getItfs' xs ys
        getItfs' [] ys = ys

getCmds :: Itf a -> [Cmd a]
getCmds (MkItf _ _ xs) = xs

collectINames :: [Itf a] -> [Id]
collectINames ((MkItf itf _ _) : xs) = itf : (collectINames xs)
collectINames [] = []

getDataTs :: [TopTm a] -> [DataT a]
getDataTs xs = getDataTs' xs []
  where getDataTs' :: [TopTm a] -> [DataT a] -> [DataT a]
        getDataTs' ((MkDataTm dt) : xs) ys = getDataTs' xs (dt : ys)
        getDataTs' (_ : xs) ys = getDataTs' xs ys
        getDataTs' [] ys = ys

getCtrs :: DataT a -> [Ctr a]
getCtrs (MkDT _ _ xs) = xs

collectDTNames :: [DataT a] -> [Id]
collectDTNames ((MkDT dt _ _) : xs) = dt : (collectDTNames xs)
collectDTNames [] = []

getDefs :: NotRaw a => [TopTm a] -> [MHDef a]
getDefs xs = getDefs' xs []
  where getDefs' :: NotRaw a => [TopTm a] -> [MHDef a] -> [MHDef a]
        getDefs' ((MkDefTm def) : xs) ys = getDefs' xs (def : ys)
        getDefs' (_ : xs) ys = getDefs' xs ys
        getDefs' [] ys = ys

-- Convert ability to a list of interface names and effect variables
{-
abToList :: Ab a -> [Id]
abToList MkEmpAb = []
abToList (MkAbVar id) = [id]
abToList MkOpenAb = []
abToList (MkAbPlus ab id _) = id : abToList ab

-- Substitute the ability for the distinguished effect variable in the type.
substOpenAb :: Ab a -> VType a -> VType a
substOpenAb ab (MkDTTy id abs xs) =
  MkDTTy id (map (substOpenAbAb ab) abs) (map (substOpenAb ab) xs)
substOpenAb ab (MkSCTy cty) = MkSCTy $ substOpenAbCType ab cty
substOpenAb _ ty = ty

substOpenAbAb :: Ab a -> Ab a -> Ab a
substOpenAbAb ab MkEmpAb = MkEmpAb
substOpenAbAb ab MkOpenAb = ab
substOpenAbAb ab (MkAbVar x) = MkAbVar x
substOpenAbAb ab (MkAbPlus ab' x ts) =
  MkAbPlus (substOpenAbAb ab' ab) x (map (substOpenAb ab) ts)

substOpenAbAdj :: Ab a -> Adj a -> Adj a
substOpenAbAdj ab MkIdAdj = MkIdAdj
substOpenAbAdj ab (MkAdjPlus adj itf xs) =
  MkAdjPlus (substOpenAbAdj ab adj) itf (map (substOpenAb ab) xs)

substOpenAbCType :: Ab a -> CType a -> CType a
substOpenAbCType ab (MkCType ps q) =
  MkCType (map (substOpenAbPort ab) ps) (substOpenAbPeg ab q)

substOpenAbPeg :: Ab a -> Peg a -> Peg a
substOpenAbPeg ab (MkPeg ab' ty) =
  MkPeg (substOpenAbAb ab ab') (substOpenAb ab ty)

substOpenAbPort :: Ab a -> Port a -> Port a
substOpenAbPort ab (MkPort adj ty) =
  MkPort (substOpenAbAdj ab adj) (substOpenAb ab ty)
-}

plus :: Ab a -> Adj a -> Ab a
plus (MkAb v m) (MkAdj m') = MkAb v (M.union m' m)

getOpName :: Operator -> Id
getOpName (MkMono x) = x
getOpName (MkPoly x) = x
getOpName (MkCmdId x) = x

-- Syntax pretty printing facilities

(<+>) = (PP.<+>)
(<>) = (PP.<>)
text = PP.text

type Doc = PP.Doc

-- Only to be applied to identifiers representing rigid or flexible
-- metavariables (type or effect).
trimVar :: Id -> Id
trimVar = takeWhile (/= '$')

-- Set to True by the main entry point if relevant flag detected.
debugMode :: IORef Bool
{-# NOINLINE debugMode #-}
debugMode = unsafePerformIO (newIORef False)

inDebugMode :: Bool
{-# NOINLINE inDebugMode #-}
inDebugMode = unsafePerformIO (readIORef debugMode)

ppVType :: VType a -> Doc
ppVType (MkDTTy x ts) = text x <+> foldl (<+>) PP.empty (map ppTyArg ts)
ppVType (MkSCTy (MkCType ps q)) = text "{" <> ports <> peg <> text "}"
  where
    ports = case map ppPort ps of
      [] -> PP.empty
      xs -> foldl (\acc x -> x <+> text "-> " <> acc) PP.empty (reverse xs)

    peg = ppPeg q
ppVType (MkTVar x) = text x
ppVType (MkRTVar x) = if inDebugMode then text x else text $ trimVar x
ppVType (MkFTVar x) = if inDebugMode then text x else text $ trimVar x
ppVType MkStringTy = text "String"
ppVType MkIntTy = text "Int"
ppVType MkCharTy = text "Char"

ppTyArg :: TyArg a -> Doc
ppTyArg (VArg t) = ppParenVType t
ppTyArg (EArg ab) = text "[" <> ppAb ab <> text "]"

ppParenVType :: VType a -> Doc
ppParenVType v@(MkDTTy _ _) = text "(" <+> ppVType v <+> text ")"
ppParenVType v = ppVType v

ppPort :: Port a -> Doc
ppPort (MkPort adj ty) = ppAdj adj <> ppVType ty

ppPeg :: Peg a -> Doc
ppPeg (MkPeg ab ty) = ppAb ab <> ppVType ty

ppAdj :: Adj a -> Doc
ppAdj (MkAdj m) | M.null m = PP.empty
ppAdj (MkAdj m) = text "<" <> ppItfMap m <> text ">"

ppAb :: Ab a -> Doc
ppAb (MkAb v m) | M.null m = text "[" <> ppAbMod v <> text "]"
ppAb (MkAb v m) =
  text "[" <> ppAbMod v <> PP.comma <+> ppItfMap m <> text "]"

ppAbMod :: AbMod a -> Doc
ppAbMod MkEmpAb = text "0"
ppAbMod (MkAbVar x) = text x
ppAbMod (MkAbRVar x) = if inDebugMode then text x else text $ trimVar x
ppAbMod (MkAbFVar x) = if inDebugMode then text x else text $ trimVar x

ppItfMap :: ItfMap a -> Doc
ppItfMap m = PP.hsep $ intersperse PP.comma $ map ppItfMapPair $ M.toList m
 where ppItfMapPair :: (Id, [TyArg a]) -> Doc
       ppItfMapPair (x, args) =
         text x <+> (foldl (<+>) PP.empty $ map ppTyArg args)
