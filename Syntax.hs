-- The raw abstract syntax and (refined) abstract syntax for Frank
{-# LANGUAGE DataKinds,GADTs,StandaloneDeriving, FlexibleInstances,
             UndecidableInstances, LambdaCase, KindSignatures,
             PatternSynonyms #-}
module Syntax where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List
import Data.Functor.Identity

import BwdFwd

{-- Elementary definitions --}
type Id = String

-- Top level definitions instantiate this class
class HasId a where
  getId :: a -> Id

{-- For the definition of the AST in terms of fixed-points --}

-- Fixed-point operator, takes a functor f
data Fix f = Fx (f (Fix f))
deriving instance Show (f (Fix f)) => Show (Fix f)
deriving instance Eq (f (Fix f)) => Eq (Fix f)

-- Gives the fixed-point of a functor "f" (see AST definitions),
--       parameterised by transformer "t" (e.g. AnnotT Raw)
type TFix (t :: (* -> *) -> (* -> *)) (f :: ((* -> *) -> (* -> *)) -> * -> *) = Fix (t (f t))

-- Annotation Transformer
-- Takes an annotation object "a",
--                  a functor "f",
--              recursor type "r"
data AnnotT a f r = AnnF (f r, a)
deriving instance (Show (f r), Show a) => Show (AnnotT a f r)
deriving instance (Eq (f r), Eq a) => Eq (AnnotT a f r)

-- Like TFix, but with special transformer, namely "AnnotT a"
-- Takes an annotation object "a",
--                  a functor "f"
type AnnotTFix a f = TFix (AnnotT a) f

-- Add annotation
ann :: a -> f (AnnotT a) (AnnotTFix a f) -> AnnotTFix a f
ann a v = Fx (AnnF (v, a))

-- Retrieve object + annotation
unAnn :: AnnotTFix a f -> (f (AnnotT a) (AnnotTFix a f), a)
unAnn (Fx (AnnF (v, a))) = (v, a)

-- Remove annotation
strip :: AnnotTFix a f -> f (AnnotT a) (AnnotTFix a f)
strip = fst . unAnn

-- Retrieve annotation
attr :: AnnotTFix a f -> a
attr = snd . unAnn

-- Modify annotation
modifyAnn :: a -> AnnotTFix a f -> AnnotTFix a f
modifyAnn a = ann a . strip

-- To annotate the origin of a node to it
data Source = InCode (Integer, Integer)
            | BuiltIn
            | Implicit
            | ImplicitNear (Integer, Integer)
            | Generated
  deriving (Show, Eq)

class HasSource a where
  getSource :: a -> Source
instance HasSource a => HasSource (AnnotTFix a f) where
  getSource x = getSource (attr x)

implicitNear :: HasSource a => a -> Source
implicitNear v = case getSource v of InCode (line, col) -> ImplicitNear (line, col)
                                     _                  -> Implicit

{-- Syntax annotations: raw syntax comes from the parser and is preprocessed
    into refined syntax. --}

class NotRaw a where
  idNotRaw :: a -> a
instance NotRaw () where idNotRaw = Prelude.id
instance NotRaw (AnnotT a Identity ()) where idNotRaw = Prelude.id

class NotDesugared a where
  idNotDesugared :: a -> a

-- output from the parser
newtype Raw = Raw Source
  deriving (Show, Eq)
instance NotDesugared Raw where idNotDesugared = Prelude.id
instance NotDesugared (AnnotT Raw Identity ()) where idNotDesugared = Prelude.id
instance NotDesugared (AnnotT Refined Identity ()) where idNotDesugared = Prelude.id
instance HasSource Raw where getSource (Raw s) = s

-- well-formed AST (after tidying up the output from the parser)
newtype Refined = Refined Source
  deriving (Show, Eq)
instance NotDesugared Refined where idNotDesugared = Prelude.id
instance NotRaw Refined where idNotRaw = Prelude.id
instance HasSource Refined where getSource (Refined s) = s

-- desugaring of types:
--   * type variables are given unique names
--   * strings are lists of characters
newtype Desugared = Desugared Source
  deriving (Show, Eq)
instance NotRaw Desugared where idNotRaw = Prelude.id
instance HasSource Desugared where getSource (Desugared s) = s

{-- The raw syntax as parsed in from the file and the refined syntax produced
    by a preprocessing stage before typechecking are simultaneously defined
    using GADT syntax. --}

data Prog t = MkProg [TopTm t]
deriving instance Show t => Show (Prog t)
deriving instance Eq t => Eq (Prog t)

{- AST nodes -}

-- Parts of the grammar are specific to raw/refined syntax. These parts are
-- marked by AnnotT Raw/Refined.

-- A top-level multihandler signature and clause.
data MHSigF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkSig :: Id -> CType Raw -> MHSigF (AnnotT Raw) r
deriving instance (Show r, Show (TFix t MHSigF)) => Show (MHSigF t r)
deriving instance (Eq r, Eq (TFix t MHSigF)) => Eq (MHSigF t r)
type MHSig a = AnnotTFix a MHSigF
pattern Sig x cty a = Fx (AnnF (MkSig x cty, a))
instance HasId (MHSig t) where getId (Sig x _ _) = x

data MHClsF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkMHCls :: Id -> Clause Raw -> MHClsF (AnnotT Raw) r
deriving instance (Show r, Show (TFix t MHClsF)) => Show (MHClsF t r)
deriving instance (Eq r, Eq (TFix t MHClsF)) => Eq (MHClsF t r)
type MHCls a = AnnotTFix a MHClsF
pattern MHCls x cls a = Fx (AnnF (MkMHCls x cls, a))
instance HasId (MHCls t) where getId (MHCls x _ _) = x

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
data MHDefF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkDef :: Id -> TFix t CTypeF -> [TFix t ClauseF] -> MHDefF t r
deriving instance (Show r, Show (TFix t CTypeF), Show (TFix t ClauseF), Show (TFix t MHDefF)) => Show (MHDefF t r)
deriving instance (Eq r, Eq (TFix t CTypeF), Eq (TFix t ClauseF), Eq (TFix t MHDefF)) => Eq (MHDefF t r)
type MHDef a = AnnotTFix a MHDefF
pattern Def x cty clss a = Fx (AnnF (MkDef x cty clss, a))
instance HasId (MHDef t) where getId (Def x _ _ _) = x

{- MH here = 'operator' in the paper. Operator here doesn't have a name
   in the paper. -}

data OperatorF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkMono :: Id -> OperatorF t r  -- monotypic (just variable)
  MkPoly :: Id -> OperatorF t r  -- polytypic  (handler expecting arguments, could also be 0 args (!))
  MkCmdId :: Id -> OperatorF t r
deriving instance (Show r, Show (TFix t OperatorF)) => Show (OperatorF t r)
deriving instance (Eq r, Eq (TFix t OperatorF)) => Eq (OperatorF t r)
type Operator a = AnnotTFix a OperatorF
pattern Mono x a = Fx (AnnF (MkMono x, a))
pattern Poly x a = Fx (AnnF (MkPoly x, a))
pattern CmdId x a = Fx (AnnF (MkCmdId x, a))

data DataConF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkDataCon :: Id -> [TFix t TmF] -> DataConF t r
deriving instance (Show r, Show (TFix t TmF), Show (TFix t DataConF)) => Show (DataConF t r)
deriving instance (Eq r, Eq (TFix t TmF), Eq (TFix t DataConF)) => Eq (DataConF t r)
type DataCon a = AnnotTFix a DataConF
pattern DataCon x tms a = Fx (AnnF (MkDataCon x tms, a))

{---------------}
{- Parts of the grammar independent of the syntax. -}

-- A raw term collects multihandler signatures and clauses separately. A
-- refined top-level term collects multihandler signatures and clauses in one
-- definition.
data TopTmF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkDataTm :: TFix t DataTF -> TopTmF t r
  MkItfTm :: TFix t ItfF -> TopTmF t r
  MkItfAliasTm :: TFix t ItfAliasF -> TopTmF t r
  MkSigTm :: TFix (AnnotT Raw) MHSigF -> TopTmF (AnnotT Raw) r
  MkClsTm :: TFix (AnnotT Raw) MHClsF -> TopTmF (AnnotT Raw) r
  MkDefTm :: NotRaw (t Identity ()) => TFix t MHDefF -> TopTmF t r
  -- MkDefTm :: NotRaw t => MHDef t -> TopTmF t r
deriving instance (Show (TFix t DataTF),
                   Show (TFix t ItfF),
                   Show (TFix t ItfAliasF),
                   Show (TFix (AnnotT Raw) MHSigF),
                   Show (TFix (AnnotT Raw) MHClsF),
                   Show (TFix t MHDefF),
                   Show r, Show (TFix t TopTmF)) => Show (TopTmF t r)
deriving instance (Eq (TFix t DataTF),
                   Eq (TFix t ItfF),
                   Eq (TFix t ItfAliasF),
                   Eq (TFix (AnnotT Raw) MHSigF),
                   Eq (TFix (AnnotT Raw) MHClsF),
                   Eq (TFix t MHDefF),
                   Eq r, Eq (TFix t TopTmF)) => Eq (TopTmF t r)
type TopTm a = AnnotTFix a TopTmF
pattern DataTm dt a = Fx (AnnF (MkDataTm dt, a))
pattern ItfTm itf a = Fx (AnnF (MkItfTm itf, a))
pattern ItfAliasTm itfAl a = Fx (AnnF (MkItfAliasTm itfAl, a))
pattern SigTm sig a = Fx (AnnF (MkSigTm sig, a))
pattern ClsTm cls a = Fx (AnnF (MkClsTm cls, a))
pattern DefTm def a = Fx (AnnF (MkDefTm def, a))
-- TODO: LC: Automatic generation of the following? Should be possible somehow
instance HasId (TopTm t) where getId (DataTm dt _) = getId dt
                               getId (ItfTm itf _) = getId itf
                               getId (ItfAliasTm itfAl _) = getId itfAl
                               getId (SigTm sig _) = getId sig
                               getId (ClsTm cls _) = getId cls
                               getId (DefTm def _) = getId def

data UseF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkRawId :: Id -> UseF (AnnotT Raw) r
  MkRawComb :: r -> [TFix (AnnotT Raw) TmF] -> UseF (AnnotT Raw) r
  MkOp :: NotRaw (t Identity ()) => TFix t OperatorF -> UseF t r
  MkApp :: NotRaw (t Identity ()) => r -> [TFix t TmF] -> UseF t r
  MkLift :: S.Set Id -> r -> UseF t r
deriving instance (Show (TFix t OperatorF),
                   Show (TFix t TmF),
                   Show (TFix t ItfMapF),
                   Show r, Show (TFix t UseF)) => Show (UseF t r)
deriving instance (Eq (TFix t OperatorF),
                   Eq (TFix t TmF),
                   Eq (TFix t ItfMapF),
                   Eq r, Eq (TFix t UseF)) => Eq (UseF t r)
type Use a = AnnotTFix a UseF
pattern RawId x a = Fx (AnnF (MkRawId x, a))
pattern RawComb f xs a = Fx (AnnF (MkRawComb f xs, a))
pattern Op op a = Fx (AnnF (MkOp op, a))
pattern App f xs a = Fx (AnnF (MkApp f xs, a))
pattern Lift itfs tm a = Fx (AnnF (MkLift itfs tm, a))

-- Tm here = 'construction' in the paper

data TmF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkSC :: TFix t SCompF -> TmF t r
  MkLet :: Id -> r -> r -> TmF (AnnotT Raw) r
  MkStr :: String -> TmF t r
  MkInt :: Integer -> TmF t r
  MkChar :: Char -> TmF t r
  MkList :: [r] -> TmF (AnnotT Raw) r
  MkTmSeq :: r -> r -> TmF t r
  MkUse :: TFix t UseF -> TmF t r
  MkDCon :: NotRaw (t Identity ()) => TFix t DataConF -> TmF t r
deriving instance (Show (TFix t SCompF),
                   Show (TFix t UseF),
                   Show (TFix t DataConF),
                   Show r, Show (TFix t TmF)) => Show (TmF t r)
deriving instance (Eq (TFix t SCompF),
                   Eq (TFix t UseF),
                   Eq (TFix t DataConF),
                   Eq r, Eq (TFix t TmF)) => Eq (TmF t r)
type Tm a = AnnotTFix a TmF
pattern SC sc a = Fx (AnnF (MkSC sc, a))
pattern Let x tm1 tm2 a = Fx (AnnF (MkLet x tm1 tm2, a))
pattern StrTm str a = Fx (AnnF (MkStr str, a))
pattern IntTm n a = Fx (AnnF (MkInt n, a))
pattern CharTm c a = Fx (AnnF (MkChar c, a))
pattern ListTm xs a = Fx (AnnF (MkList xs, a))
pattern TmSeq tm1 tm2 a = Fx (AnnF (MkTmSeq tm1 tm2, a))
pattern Use u a = Fx (AnnF (MkUse u, a))
pattern DCon dc a = Fx (AnnF (MkDCon dc, a))

-- A clause for a multihandler definition
data ClauseF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkCls :: [TFix t PatternF] -> TFix t TmF -> ClauseF t r
deriving instance (Show (TFix t PatternF),
                   Show (TFix t TmF),
                   Show r, Show (TFix t ClauseF)) => Show (ClauseF t r)
deriving instance (Eq (TFix t PatternF),
                   Eq (TFix t TmF),
                   Eq r, Eq (TFix t ClauseF)) => Eq (ClauseF t r)
type Clause a = AnnotTFix a ClauseF
pattern Cls ps t a = Fx (AnnF (MkCls ps t, a))

data SCompF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkSComp :: [TFix t ClauseF] -> SCompF t r
deriving instance (Show (TFix t ClauseF),
                   Show r, Show (TFix t SCompF)) => Show (SCompF t r)
deriving instance (Eq (TFix t ClauseF),
                   Eq r, Eq (TFix t SCompF)) => Eq (SCompF t r)
type SComp a = AnnotTFix a SCompF
pattern SComp cls a = Fx (AnnF (MkSComp cls, a))

data Kind = VT   -- value type
          | ET   -- effect type
  deriving (Show, Eq)

data DataTF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkDT :: Id -> [(Id, Kind)] -> [TFix t CtrF] -> DataTF t r
deriving instance (Show (TFix t CtrF),
                   Show r, Show (TFix t DataTF)) => Show (DataTF t r)
deriving instance (Eq (TFix t CtrF),
                   Eq r, Eq (TFix t DataTF)) => Eq (DataTF t r)
type DataT a = AnnotTFix a DataTF
pattern DT x ps ctrs a = Fx (AnnF (MkDT x ps ctrs, a))
instance HasId (DataT t) where getId (DT x _ _ _) = x

data ItfF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkItf :: Id -> [(Id, Kind)] -> [TFix t CmdF] -> ItfF t r
deriving instance (Show (TFix t CmdF),
                   Show r, Show (TFix t ItfF)) => Show (ItfF t r)
deriving instance (Eq (TFix t CmdF),
                   Eq r, Eq (TFix t ItfF)) => Eq (ItfF t r)
type Itf a = AnnotTFix a ItfF
pattern Itf x ps cmds a = Fx (AnnF (MkItf x ps cmds, a))
instance HasId (Itf t) where getId (Itf x _ _ _) = x

data ItfAliasF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkItfAlias :: Id -> [(Id, Kind)] -> TFix t ItfMapF -> ItfAliasF t r
deriving instance (Show (TFix t ItfMapF),
                   Show r, Show (TFix t ItfAliasF)) => Show (ItfAliasF t r)
deriving instance (Eq (TFix t ItfMapF),
                   Eq r, Eq (TFix t ItfAliasF)) => Eq (ItfAliasF t r)
type ItfAlias a = AnnotTFix a ItfAliasF
pattern ItfAlias x ps itfMap a = Fx (AnnF (MkItfAlias x ps itfMap, a))
instance HasId (ItfAlias t) where getId (ItfAlias x _ _ _) = x

data CtrF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkCtr :: Id -> [TFix t VTypeF] -> CtrF t r
deriving instance (Show (TFix t VTypeF),
                   Show r, Show (TFix t CtrF)) => Show (CtrF t r)
deriving instance (Eq (TFix t VTypeF),
                   Eq r, Eq (TFix t CtrF)) => Eq (CtrF t r)
type Ctr a = AnnotTFix a CtrF
pattern Ctr x tys a = Fx (AnnF (MkCtr x tys, a))

data CmdF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkCmd :: Id -> [(Id, Kind)] -> [TFix t VTypeF] -> TFix t VTypeF -> CmdF t r
deriving instance (Show (TFix t VTypeF),
                   Show r, Show (TFix t CmdF)) => Show (CmdF t r)
deriving instance (Eq (TFix t VTypeF),
                   Eq r, Eq (TFix t CmdF)) => Eq (CmdF t r)
--                    id  ty vars      arg tys   result ty
type Cmd a = AnnotTFix a CmdF
pattern Cmd x ps tys ty a = Fx (AnnF (MkCmd x ps tys ty, a))

data PatternF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkVPat :: TFix t ValuePatF -> PatternF t r
  MkCmdPat :: Id -> Int -> [TFix t ValuePatF] -> Id -> PatternF t r
  MkThkPat :: Id -> PatternF t r
deriving instance (Show (TFix t ValuePatF),
                   Show r, Show (TFix t PatternF)) => Show (PatternF t r)
deriving instance (Eq (TFix t ValuePatF),
                   Eq r, Eq (TFix t PatternF)) => Eq (PatternF t r)
type Pattern a = AnnotTFix a PatternF
pattern VPat vp a = Fx (AnnF (MkVPat vp, a))
pattern CmdPat x n vps k a = Fx (AnnF (MkCmdPat x n vps k, a))
pattern ThkPat x a = Fx (AnnF (MkThkPat x, a))

-- TODO: should we compile away string patterns into list of char patterns?
-- Takes      tag "t" (e.g. Refined),
--       recursor "r"
data ValuePatF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkVarPat :: Id -> ValuePatF t r
  MkDataPat :: Id -> [r] -> ValuePatF t r
  MkIntPat :: Integer -> ValuePatF t r
  MkCharPat :: Char -> ValuePatF t r
  MkStrPat :: String -> ValuePatF t r
  MkConsPat :: r -> r -> ValuePatF (AnnotT Raw) r
  MkListPat :: [r] -> ValuePatF (AnnotT Raw) r
deriving instance (Show r, Show (TFix t ValuePatF)) => Show (ValuePatF t r)
deriving instance (Eq r, Eq (TFix t ValuePatF)) => Eq (ValuePatF t r)
type ValuePat a = AnnotTFix a ValuePatF
pattern VarPat x a = Fx (AnnF (MkVarPat x, a))
pattern DataPat x vps a = Fx (AnnF (MkDataPat x vps, a))
pattern IntPat n a = Fx (AnnF (MkIntPat n, a))
pattern CharPat c a = Fx (AnnF (MkCharPat c, a))
pattern StrPat str a = Fx (AnnF (MkStrPat str, a))
pattern ConsPat p1 p2 a = Fx (AnnF (MkConsPat p1 p2, a))
pattern ListPat ps a = Fx (AnnF (MkListPat ps, a))

-- Type hierarchy
data CTypeF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkCType :: [TFix t PortF] -> TFix t PegF -> CTypeF t r        -- computation types
deriving instance (Show (TFix t PortF),
                   Show (TFix t PegF),
                   Show r, Show (TFix t CTypeF)) => Show (CTypeF t r)
deriving instance (Eq (TFix t PortF),
                   Eq (TFix t PegF),
                   Eq r, Eq (TFix t CTypeF)) => Eq (CTypeF t r)
type CType a = AnnotTFix a CTypeF
pattern CType ports peg a = Fx (AnnF (MkCType ports peg, a))

data PortF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkPort :: TFix t AdjF -> TFix t VTypeF -> PortF t r           -- ports
deriving instance (Show (TFix t AdjF),
                   Show (TFix t VTypeF),
                   Show r, Show (TFix t PortF)) => Show (PortF t r)
deriving instance (Eq (TFix t AdjF),
                   Eq (TFix t VTypeF),
                   Eq r, Eq (TFix t PortF)) => Eq (PortF t r)
type Port a = AnnotTFix a PortF
pattern Port adj ty a = Fx (AnnF (MkPort adj ty, a))

data PegF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkPeg :: TFix t AbF -> TFix t VTypeF -> PegF t r              -- pegs
deriving instance (Show (TFix t AbF),
                   Show (TFix t VTypeF),
                   Show r, Show (TFix t PegF)) => Show (PegF t r)
deriving instance (Eq (TFix t AbF),
                   Eq (TFix t VTypeF),
                   Eq r, Eq (TFix t PegF)) => Eq (PegF t r)
type Peg a = AnnotTFix a PegF
pattern Peg ab ty a = Fx (AnnF (MkPeg ab ty, a))

data VTypeF :: ((* -> *) -> (* -> *)) -> * -> * where           -- value types
  MkDTTy :: Id -> [TFix t TyArgF] -> VTypeF t r               --   data types (instant. type constr.)  may be refined to MkTVar
  MkSCTy :: TFix t CTypeF -> VTypeF t  r                        --   suspended computation types
  MkTVar :: NotDesugared (t Identity ()) => Id -> VTypeF t  r   --                                       may be refined to MkDTTy
  MkRTVar :: Id -> VTypeF (AnnotT Desugared)  r                 --   rigid type variable (bound)
  MkFTVar :: Id -> VTypeF (AnnotT Desugared)  r                 --   flexible type variable (free)
  MkStringTy :: NotDesugared (t Identity ()) => VTypeF t r      --   string type
  MkIntTy :: VTypeF t r                                         --   int type
  MkCharTy :: VTypeF t r                                        --   char type
deriving instance (Show (TFix t TyArgF),
                   Show (TFix t CTypeF),
                   Show r, Show (TFix t VTypeF)) => Show (VTypeF t r)
deriving instance (Eq (TFix t TyArgF),
                   Eq (TFix t CTypeF),
                   Eq r, Eq (TFix t VTypeF)) => Eq (VTypeF t r)
type VType a = AnnotTFix a VTypeF
pattern DTTy x tyArgs a = Fx (AnnF (MkDTTy x tyArgs, a))
pattern SCTy cty a = Fx (AnnF (MkSCTy cty, a))
pattern TVar x a = Fx (AnnF (MkTVar x, a))
pattern RTVar x a = Fx (AnnF (MkRTVar x, a))
pattern FTVar x a = Fx (AnnF (MkFTVar x, a))
pattern StringTy a = Fx (AnnF (MkStringTy, a))
pattern IntTy a = Fx (AnnF (MkIntTy, a))
pattern CharTy a = Fx (AnnF (MkCharTy, a))

-- Interface-id -> list of bwd-list of ty arg's (each entry an instantiation)
data ItfMapF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkItfMap :: M.Map Id (Bwd [TFix t TyArgF]) -> ItfMapF t r
deriving instance (Show (TFix t TyArgF),
                   Show r, Show (TFix t ItfMapF)) => Show (ItfMapF t r)
deriving instance (Eq (TFix t TyArgF),
                   Eq r, Eq (TFix t ItfMapF)) => Eq (ItfMapF t r)
type ItfMap a = AnnotTFix a ItfMapF
pattern ItfMap m a = Fx (AnnF (MkItfMap m, a))

-- Adjustments (set of instantiated interfaces)
data AdjF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkAdj :: TFix t ItfMapF -> AdjF t r -- interface-id -> list of ty arg's
deriving instance (Show (TFix t ItfMapF),
                   Show r, Show (TFix t AdjF)) => Show (AdjF t r)
deriving instance (Eq (TFix t ItfMapF),
                   Eq r, Eq (TFix t AdjF)) => Eq (AdjF t r)
type Adj a = AnnotTFix a AdjF
pattern Adj itfMap a = Fx (AnnF (MkAdj itfMap, a))

-- Abilities
data AbF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkAb :: TFix t AbModF -> TFix t ItfMapF -> AbF t r            -- interface-id  ->  list of ty arg's
deriving instance (Show (TFix t AbModF),
                   Show (TFix t ItfMapF),
                   Show r, Show (TFix t AbF)) => Show (AbF t r)
deriving instance (Eq (TFix t AbModF),
                   Eq (TFix t ItfMapF),
                   Eq r, Eq (TFix t AbF)) => Eq (AbF t r)
type Ab a = AnnotTFix a AbF
pattern Ab abMod itfMap a = Fx (AnnF (MkAb abMod itfMap, a))

-- Ability modes
data AbModF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkEmpAb :: AbModF t r                                         -- empty            (closed ability)
  MkAbVar :: NotDesugared (t Identity ()) => Id -> AbModF t r   -- non-desugared effect variable
  MkAbRVar :: Id -> AbModF (AnnotT Desugared)  r                -- rigid eff var    (open ability)
  MkAbFVar :: Id -> AbModF (AnnotT Desugared)  r                -- flexible eff var (open ability)
deriving instance (Show r, Show (TFix t AbModF)) => Show (AbModF t r)
deriving instance (Eq r, Eq (TFix t AbModF)) => Eq (AbModF t r)
type AbMod a = AnnotTFix a AbModF
pattern EmpAb a = Fx (AnnF (MkEmpAb, a))
pattern AbVar x a = Fx (AnnF (MkAbVar x, a))
pattern AbRVar x a = Fx (AnnF (MkAbRVar x, a))
pattern AbFVar x a = Fx (AnnF (MkAbFVar x, a))

data TyArgF :: ((* -> *) -> (* -> *)) -> * -> * where
  MkVArg :: TFix t VTypeF -> TyArgF t r
  MkEArg :: TFix t AbF   -> TyArgF t r
deriving instance (Show (TFix t VTypeF),
                   Show (TFix t AbF),
                   Show r, Show (TFix t TyArgF)) => Show (TyArgF t r)
deriving instance (Eq (TFix t VTypeF),
                   Eq (TFix t AbF),
                   Eq r, Eq (TFix t TyArgF)) => Eq (TyArgF t r)
type TyArg a = AnnotTFix a TyArgF
pattern VArg ty a = Fx (AnnF (MkVArg ty, a))
pattern EArg ab a = Fx (AnnF (MkEArg ab, a))

idAdjRaw :: Adj Raw
idAdjRaw = Adj (ItfMap M.empty (Raw Implicit)) (Raw Implicit)

idAdjRef :: Adj Refined
idAdjRef = Adj (ItfMap M.empty (Refined Implicit)) (Refined Implicit)

idAdjDesug :: Adj Desugared
idAdjDesug = Adj (ItfMap M.empty (Desugared Implicit)) (Desugared Implicit)

desugaredStrTy :: Desugared -> VType Desugared
desugaredStrTy a = DTTy "List" [VArg (CharTy a) a] a

getCmds :: Itf t -> [Cmd t]
getCmds (Itf _ _ xs _) = xs

collectINames :: [Itf t] -> [Id]
collectINames = map (\case (Itf itf _ _ _) -> itf)

getCtrs :: DataT t -> [Ctr t]
getCtrs (DT _ _ xs _) = xs

collectDTNames :: [DataT t] -> [Id]
collectDTNames = map (\case (DT dt _ _ _) -> dt)

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

-- ability (1st arg) might be overridden by adjustment (2nd arg)
plus :: Ab t -> Adj t -> Ab t
plus (Ab v m a) (Adj m' _) = Ab v (m `plusItfMap` m') a

getOpName :: Operator t -> Id
getOpName (Mono x _) = x
getOpName (Poly x _) = x
getOpName (CmdId x _) = x

-- transform type variable (+ its kind) to a raw tye variable argument
-- (use during refinement of itf maps)
tyVar2rawTyVarArg :: (Id, Kind) -> TyArg Raw
tyVar2rawTyVarArg (id, VT) = VArg (TVar id (Raw Generated)) (Raw Generated)
tyVar2rawTyVarArg (id, ET) = EArg (liftAbMod (AbVar id (Raw Generated))) (Raw Generated)

-- transform type variable (+ its kind) to a rigid tye variable argument
-- (prepare for later unification)
tyVar2rigTyVarArg :: (Id, Kind) -> TyArg Desugared
tyVar2rigTyVarArg (id, VT) = VArg (RTVar id (Desugared Generated)) (Desugared Generated)
tyVar2rigTyVarArg (id, ET) = EArg (liftAbMod (AbRVar id (Desugared Generated))) (Desugared Generated)

liftAbMod :: AbMod t -> Ab t
liftAbMod abMod = Ab abMod (ItfMap M.empty (attr abMod)) (attr abMod)

-- Only to be applied to identifiers representing rigid or flexible
-- metavariables (type or effect).
trimVar :: Id -> Id
trimVar = takeWhile (/= '$')

{- Operations on interface maps -}

-- For each interface, the instances are concatenated
-- e.g. [State Bool, State Int] + [State String, State Char] =
-- [State Bool, State Int, State String, State Char]
plusItfMap :: ItfMap t -> ItfMap t -> ItfMap t
plusItfMap (ItfMap m a) (ItfMap m' _) = foldl plusItfMap' (ItfMap m a) (M.toList m')
  where plusItfMap' :: ItfMap t -> (Id, Bwd [TyArg t]) -> ItfMap t
        plusItfMap' (ItfMap m'' a'') (x, instants) = if M.member x m'' then ItfMap (M.adjust (\instants' -> instants' <>< bwd2fwd instants) x m'') a''
                                                                       else ItfMap (M.insert x instants m'') a''

-- eg. [State Bool,State Int] + State Char = [State Bool,State Int,State Char]
addInstanceToItfMap :: ItfMap Raw -> (Id, [TyArg Raw]) -> ItfMap Raw
addInstanceToItfMap (ItfMap m a) (x, args) =
  if M.member x m then ItfMap (M.adjust (:< args) x m) a
  else ItfMap (M.insert x (BEmp :< args) m) a

-- Given m1 and m2, return
-- 1) All interfaces that occur in m1 *and* m2
-- 2) Of those interface, take only the longest suffix of common length,
--    with instances from m1
intersectItfMap :: ItfMap t -> ItfMap t -> ItfMap t
intersectItfMap (ItfMap m1 a) (ItfMap m2 _) = ItfMap m'' a
  where m'  = M.intersectionWith (\args args' -> takeBwd (min (length args) (length args')) args) m1 m2
        m'' = M.filter (not . null) m'

-- Given m1 and m2, cut off entry suffixes of m1 of length determined by m2's
-- entries' lengths
cutItfMapSuffix :: ItfMap t -> ItfMap t -> ItfMap t
cutItfMapSuffix (ItfMap m1 a) (ItfMap m2 _) = ItfMap m'' a
  where m' = M.differenceWith (\args args' -> Just $ dropBwd (length args') args) m1 m2
        m'' = M.filter (not . null) m'

stripInactiveOffItfMap :: ItfMap t -> ItfMap t
stripInactiveOffItfMap (ItfMap m a) = ItfMap m' a
  where m' = M.map (\case BEmp -> error "invariant broken"
                          (_ :< x) -> BEmp :< x) m

isItfMapSuffixOf :: Eq t => ItfMap t -> ItfMap t -> Bool
isItfMapSuffixOf m1 m2 = (m2 `cutItfMapSuffix` m1) `plusItfMap` m1 == m2

emptyItfMap :: t -> ItfMap t
emptyItfMap = ItfMap M.empty

isItfMapEmpty :: ItfMap t -> Bool
isItfMapEmpty (ItfMap m _) = M.null m

-- Remove from the map the first instance of every interface in the set.
removeItfs :: ItfMap t -> S.Set Id -> ItfMap t
removeItfs (ItfMap m a) p =
  let upd sx = case sx of
        BEmp -> error "lift invariant broken"
        BEmp :< _ -> Nothing
        sy :< _ -> Just sy
  in
   ItfMap (S.foldr (\k q -> M.update upd k q) m p) a
