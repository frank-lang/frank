{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}

-- The raw abstract syntax and (refined) abstract syntax for Frank
module Syntax where

import qualified Data.Map.Strict as M
import Data.List

{-------------------}
{-- For the definition of the AST --}

data Fix f = Fx (f (Fix f))
deriving instance Show (f (Fix f)) => Show (Fix f)
deriving instance Eq (f (Fix f)) => Eq (Fix f)

data AnnotT a f r = AnnF (f r, a)
deriving instance (Show (f r), Show a) => Show (AnnotT a f r)
deriving instance (Eq (f r), Eq a) => Eq (AnnotT a f r)

type AnnotFix f a = Fix (AnnotT a (f a))

ann :: a -> f a (AnnotFix f a) -> AnnotFix f a
ann a v = (Fx (AnnF (v, a)))

unAnn :: AnnotFix f a -> (f a (AnnotFix f a), a)
unAnn (Fx (AnnF (v, a))) = (v, a)

strip :: AnnotFix f a -> f a (AnnotFix f a)
strip = fst . unAnn

attr :: AnnotFix f a -> a
attr = snd . unAnn

splitAnn :: Fix (AnnotT a f) -> (Fix (AnnotT a f), f (Fix (AnnotT a f)), a)
splitAnn x@(Fx (AnnF (v, a))) = (x , v, a)

liftAnn :: (Monad m) => (f a (AnnotFix f a) -> m (f a (AnnotFix f a))) -> AnnotFix f a -> m (AnnotFix f a)
liftAnn f (unAnn -> (v, a)) = ann a <$> f v

keepAnn :: (f a (AnnotFix f a) -> f a (AnnotFix f a)) -> AnnotFix f a -> AnnotFix f a
keepAnn f (unAnn -> (v, a)) = ann a (f v)

data Source = InCode (Integer, Integer)
            | BuiltIn
            | Implicit
            | ImplicitNear (Integer, Integer)
            | Generated
  deriving (Show, Eq)

class HasSource a where
  getSource :: a -> Source
instance HasSource a => HasSource (AnnotFix f a) where
  getSource x = getSource (attr x)

implicitNear :: HasSource a => a -> Source
implicitNear v = case getSource v of InCode (line, col) -> ImplicitNear (line, col)
                                     _                  -> Implicit

{-------------------}
{-- Syntax description: raw syntax comes from the parser and preprocessed into
    refined syntax. --}

class NotRaw a where
  idNotRaw :: a -> a

class NotDesugared a where
  idNotDesugared :: a -> a

-- output from the parser
newtype Raw = Raw Source
  deriving (Show, Eq)
instance NotDesugared Raw where idNotDesugared = Prelude.id
instance HasSource Raw where getSource (Raw s) = s

instance NotRaw () where idNotRaw = Prelude.id

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

{---------------}
{- Parts of the grammar specific to the raw syntax. -}

-- A top-level multihandler signature and clause.
-- data MHSigF r = MkSig Id (CType Raw) deriving (Show, Eq)
-- type MHSig = Fix (AnnotT Source MHSigF)
data MHSigF :: * -> * -> * where
  MkSig :: Id -> CType Raw -> MHSigF Raw r
deriving instance Show (MHSigF Raw r)
deriving instance Eq (MHSigF Raw r)
type MHSig t = AnnotFix MHSigF t
pattern Sig x cty a = Fx (AnnF (MkSig x cty, a))

data MHClsF :: * -> * -> * where
  MkMHCls :: Id -> Clause Raw -> MHClsF Raw r
deriving instance Show (MHClsF t r)
deriving instance Eq (MHClsF t r)
type MHCls t = AnnotFix MHClsF t
pattern MHCls x cls a = Fx (AnnF (MkMHCls x cls, a))

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
data MHDefF :: * -> * -> * where
  MkDef :: Id -> CType t -> [Clause t] -> MHDefF t r
deriving instance Show t => Show (MHDefF t r)
deriving instance Eq t => Eq (MHDefF t r)
type MHDef t = AnnotFix MHDefF t
pattern Def x cty clss a = Fx (AnnF (MkDef x cty clss, a))
-- value bindings - not yet supported
-- data VDef a = VDef Id (VType a) (Tm a)

{- MH here = 'operator' in the paper. Operator here doesn't have a name
   in the paper. -}

data OperatorF :: * -> * -> * where
  MkMono :: Id -> OperatorF t r  -- monotypic (just variable)
  MkPoly :: Id -> OperatorF t r  -- polytypic  (handler expecting arguments, could also be 0 args (!))
  MkCmdId :: Id -> OperatorF t r
deriving instance Show t => Show (OperatorF t r)
deriving instance Eq t => Eq (OperatorF t r)
type Operator t = AnnotFix OperatorF t
pattern Mono x a = Fx (AnnF (MkMono x, a))
pattern Poly x a = Fx (AnnF (MkPoly x, a))
pattern CmdId x a = Fx (AnnF (MkCmdId x, a))

data DataConF :: * -> * -> * where
  MkDataCon :: Id -> [Tm t] -> DataConF t r
deriving instance Show t => Show (DataConF t r)
deriving instance Eq t => Eq (DataConF t r)
type DataCon t = AnnotFix DataConF t
pattern DataCon x tms a = Fx (AnnF (MkDataCon x tms, a))

{---------------}
{- Parts of the grammar independent of the syntax. -}

-- A raw term collects multihandler signatures and clauses separately. A
-- refined top-level term collects multihandler signatures and clauses in one
-- definition.
data TopTmF :: * -> * -> * where
  MkDataTm :: DataT t -> TopTmF t r
  MkItfTm :: Itf t -> TopTmF t r
  MkItfAliasTm :: ItfAlias t -> TopTmF t r
  MkSigTm :: MHSig Raw -> TopTmF Raw r
  MkClsTm :: MHCls Raw -> TopTmF Raw r
  MkDefTm :: NotRaw t => MHDef t -> TopTmF t r
deriving instance Show t => Show (TopTmF t r)
deriving instance Eq t => Eq (TopTmF t r)
type TopTm t = AnnotFix TopTmF t
pattern DataTm dt a = Fx (AnnF (MkDataTm dt, a))
pattern ItfTm itf a = Fx (AnnF (MkItfTm itf, a))
pattern ItfAliasTm itfAl a = Fx (AnnF (MkItfAliasTm itfAl, a))
pattern SigTm sig a = Fx (AnnF (MkSigTm sig, a))
pattern ClsTm cls a = Fx (AnnF (MkClsTm cls, a))
pattern DefTm def a = Fx (AnnF (MkDefTm def, a))

data UseF :: * -> * -> * where
  MkRawId :: Id -> UseF Raw r
  MkRawComb :: r -> [Tm Raw] -> UseF Raw r
  MkOp :: NotRaw t => Operator t -> UseF t r
  MkApp :: NotRaw t => r -> [Tm t] -> UseF t r
deriving instance (Show r, Show (Tm t), Show t) => Show (UseF t r)
deriving instance (Eq r, Eq (Tm t), Eq t) => Eq (UseF t r)
type Use t = AnnotFix UseF t
pattern RawId x a = Fx (AnnF (MkRawId x, a))
pattern RawComb f xs a = Fx (AnnF (MkRawComb f xs, a))
pattern Op op a = Fx (AnnF (MkOp op, a))
pattern App f xs a = Fx (AnnF (MkApp f xs, a))

-- Tm here = 'construction' in the paper

data TmF :: * -> * -> * where
  MkSC :: SComp t -> TmF t r
  MkLet :: Id -> r -> r -> TmF Raw r
  MkStr :: String -> TmF t r
  MkInt :: Integer -> TmF t r
  MkChar :: Char -> TmF t r
  MkList :: [r] -> TmF Raw r
  MkTmSeq :: r -> r -> TmF t r
  MkUse :: Use t -> TmF t r
  MkDCon :: NotRaw t => DataCon t -> TmF t r
deriving instance (Show r, Show t) => Show (TmF t r)
deriving instance (Eq r, Eq t) => Eq (TmF t r)
type Tm t = AnnotFix TmF t
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
data ClauseF :: * -> * -> * where
  MkCls :: [Pattern t] -> Tm t -> ClauseF t r
deriving instance Show t => Show (ClauseF t r)
deriving instance Eq t => Eq (ClauseF t r)
type Clause t = AnnotFix ClauseF t
pattern Cls ps t a = Fx (AnnF (MkCls ps t, a))

data SCompF :: * -> * -> * where
  MkSComp :: [Clause t] -> SCompF t r
deriving instance Show t => Show (SCompF t r)
deriving instance Eq t => Eq (SCompF t r)
type SComp t = AnnotFix SCompF t
pattern SComp cls a = Fx (AnnF (MkSComp cls, a))

data Kind = VT   -- value type
          | ET   -- effect type
  deriving (Show, Eq)

data DataTF :: * -> * -> * where
  MkDT :: Id -> [(Id, Kind)] -> [Ctr t] -> DataTF t r
deriving instance Show t => Show (DataTF t r)
deriving instance Eq t => Eq (DataTF t r)
type DataT t = AnnotFix DataTF t
pattern DT x ps ctrs a = Fx (AnnF ((MkDT x ps ctrs), a))

data ItfF :: * -> * -> * where
  MkItf :: Id -> [(Id, Kind)] -> [Cmd t] -> ItfF t r
deriving instance Show t => Show (ItfF t r)
deriving instance Eq t => Eq (ItfF t r)
type Itf t = AnnotFix ItfF t
pattern Itf x ps cmds a = Fx (AnnF (MkItf x ps cmds, a))

data ItfAliasF :: * -> * -> * where
  MkItfAlias :: Id -> [(Id, Kind)] -> (ItfMap t) -> ItfAliasF t r
deriving instance Show t => Show (ItfAliasF t r)
deriving instance Eq t => Eq (ItfAliasF t r)
type ItfAlias t = AnnotFix ItfAliasF t
pattern ItfAlias x ps itfMap a = Fx (AnnF (MkItfAlias x ps itfMap, a))

data CtrF :: * -> * -> * where
  MkCtr :: Id -> [VType t] -> CtrF t r
deriving instance Show t => Show (CtrF t r)
deriving instance Eq t => Eq (CtrF t r)
type Ctr t = AnnotFix CtrF t
pattern Ctr x tys a = Fx (AnnF (MkCtr x tys, a))

data CmdF :: * -> * -> * where
  MkCmd :: Id -> [(Id, Kind)] -> [VType t] -> VType t -> CmdF t r
deriving instance Show t => Show (CmdF t r)
deriving instance Eq t => Eq (CmdF t r)
--                    id  ty vars      arg tys   result ty
type Cmd t = AnnotFix CmdF t
pattern Cmd x ps tys ty a = Fx (AnnF (MkCmd x ps tys ty, a))

data PatternF :: * -> * -> * where
  MkVPat :: ValuePat t -> PatternF t r
  MkCmdPat :: Id -> [ValuePat t] -> Id -> PatternF t r
  MkThkPat :: Id -> PatternF t r
deriving instance Show t => Show (PatternF t r)
deriving instance Eq t => Eq (PatternF t r)
type Pattern t = AnnotFix PatternF t
pattern VPat vp a = Fx (AnnF (MkVPat vp, a))
pattern CmdPat x vps k a = Fx (AnnF (MkCmdPat x vps k, a))
pattern ThkPat x a = Fx (AnnF (MkThkPat x, a))

-- TODO: should we compile away string patterns into list of char patterns?
data ValuePatF :: * -> * -> * where
  MkVarPat :: Id -> ValuePatF t r
  MkDataPat :: Id -> [r] -> ValuePatF t r
  MkIntPat :: Integer -> ValuePatF t r
  MkCharPat :: Char -> ValuePatF t r
  MkStrPat :: String -> ValuePatF t r
  MkConsPat :: r -> r -> ValuePatF Raw r
  MkListPat :: [r] -> ValuePatF Raw r
deriving instance (Show r, Show t) => Show (ValuePatF t r)
deriving instance (Eq r, Eq t) => Eq (ValuePatF t r)
type ValuePat t = AnnotFix ValuePatF t
pattern VarPat x a = Fx (AnnF (MkVarPat x, a))
pattern DataPat x vps a = Fx (AnnF (MkDataPat x vps, a))
pattern IntPat n a = Fx (AnnF (MkIntPat n, a))
pattern CharPat c a = Fx (AnnF (MkCharPat c, a))
pattern StrPat str a = Fx (AnnF (MkStrPat str, a))
pattern ConsPat p1 p2 a = Fx (AnnF (MkConsPat p1 p2, a))
pattern ListPat ps a = Fx (AnnF (MkListPat ps, a))

type Id = String

-- Type hierarchy
data CTypeF :: * -> * -> * where
  MkCType :: [Port t] -> Peg t -> CTypeF t r     -- computation types
deriving instance Show t => Show (CTypeF t r)
deriving instance Eq t => Eq (CTypeF t r)
type CType t= AnnotFix CTypeF t
pattern CType ports peg a = Fx (AnnF (MkCType ports peg, a))

data PortF :: * -> * -> * where
  MkPort :: Adj t -> VType t -> PortF t r       -- ports
deriving instance Show t => Show (PortF t r)
deriving instance Eq t => Eq (PortF t r)
type Port t = AnnotFix PortF t
pattern Port adj ty a = Fx (AnnF (MkPort adj ty, a))

data PegF :: * -> * -> * where
  MkPeg :: Ab t -> VType t -> PegF t r          -- pegs
deriving instance Show t => Show (PegF t r)
deriving instance Eq t => Eq (PegF t r)
type Peg t = AnnotFix PegF t
pattern Peg ab ty a = Fx (AnnF (MkPeg ab ty, a))

data VTypeF :: * -> * -> * where   -- value types
  MkDTTy :: Id -> [TyArg t] -> VTypeF t r       --   data types (instant. type constr.)  may be refined to MkTVar
  MkSCTy :: CType t -> VTypeF t  r              --   suspended computation types
  MkTVar :: NotDesugared t => Id -> VTypeF t  r --                                       may be refined to MkDTTy
  MkRTVar :: Id -> VTypeF Desugared r          --   rigid type variable (bound)
  MkFTVar :: Id -> VTypeF Desugared r         --   flexible type variable (free)
  MkStringTy :: NotDesugared t => VTypeF t r   --   string type
  MkIntTy :: VTypeF t r                        --   int type
  MkCharTy :: VTypeF t r                       --   char type
deriving instance Show t => Show (VTypeF t r)
deriving instance Eq t => Eq (VTypeF t r)
type VType t = AnnotFix VTypeF t
pattern DTTy x tyArgs a = Fx (AnnF (MkDTTy x tyArgs, a))
pattern SCTy cty a = Fx (AnnF (MkSCTy cty, a))
pattern TVar x a = Fx (AnnF (MkTVar x, a))
pattern RTVar x a = Fx (AnnF (MkRTVar x, a))
pattern FTVar x a = Fx (AnnF (MkFTVar x, a))
pattern StringTy a = Fx (AnnF (MkStringTy, a))
pattern IntTy a = Fx (AnnF (MkIntTy, a))
pattern CharTy a = Fx (AnnF (MkCharTy, a))

data ItfMapF :: * -> * -> * where
  MkItfMap :: M.Map Id [TyArg t] -> ItfMapF t r           -- interface-id  ->  list of ty arg's  (each entry an instantiation)
deriving instance Show t => Show (ItfMapF t r)
deriving instance Eq t => Eq (ItfMapF t r)
type ItfMap t = AnnotFix ItfMapF t
pattern ItfMap m a = Fx (AnnF (MkItfMap m, a))

-- Adjustments (set of instantiated interfaces)
data AdjF :: * -> * -> * where
  MkAdj :: ItfMap t -> AdjF t r                -- interface-id  ->  list of ty arg's
deriving instance Show t => Show (AdjF t r)
deriving instance Eq t => Eq (AdjF t r)
type Adj t = AnnotFix AdjF t
pattern Adj itfMap a = Fx (AnnF (MkAdj itfMap, a))

-- Abilities
data AbF :: * -> * -> * where
  MkAb :: AbMod t -> ItfMap t -> AbF t r        -- interface-id  ->  list of ty arg's
deriving instance Show t => Show (AbF t r)
deriving instance Eq t => Eq (AbF t r)
type Ab t = AnnotFix AbF t
pattern Ab abMod itfMap a = Fx (AnnF (MkAb abMod itfMap, a))

-- Ability modes
data AbModF :: * -> * -> * where
  MkEmpAb :: AbModF t r                         -- empty            (closed ability)
  MkAbVar :: NotDesugared t => Id -> AbModF t r -- non-desugared effect variable
  MkAbRVar :: Id -> AbModF Desugared r         -- rigid eff var    (open ability)
  MkAbFVar :: Id -> AbModF Desugared r         -- flexible eff var (open ability)
deriving instance Show (AbModF t r)
deriving instance Eq (AbModF t r)
type AbMod t = AnnotFix AbModF t
pattern EmpAb a = Fx (AnnF (MkEmpAb, a))
pattern AbVar x a = Fx (AnnF (MkAbVar x, a))
pattern AbRVar x a = Fx (AnnF (MkAbRVar x, a))
pattern AbFVar x a = Fx (AnnF (MkAbFVar x, a))

data TyArgF :: * -> * -> * where
  MkVArg :: VType t -> TyArgF t r
  MkEArg :: Ab t    -> TyArgF t r
deriving instance Show t => Show (TyArgF t r)
deriving instance Eq t => Eq (TyArgF t r)
type TyArg t = AnnotFix TyArgF t
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

getItfs :: [TopTm t] -> [Itf t]
getItfs xs = [ itf | (ItfTm itf _) <- xs ]

getCmds :: Itf t -> [Cmd t]
getCmds (Itf _ _ xs _) = xs

getItfAliases :: [TopTm t] -> [ItfAlias t]
getItfAliases xs = [itfAlias | (ItfAliasTm itfAlias _) <- xs]

collectINames :: [Itf t] -> [Id]
collectINames = map (\case (Itf itf _ _ _) -> itf)

getDataTs :: [TopTm t] -> [DataT t]
getDataTs xs = [dt | (DataTm dt _) <- xs]

getCtrs :: DataT t -> [Ctr t]
getCtrs (DT _ _ xs _) = xs

collectDTNames :: [DataT t] -> [Id]
collectDTNames = map (\case (DT dt _ _ _) -> dt)

getDefs :: NotRaw t => [TopTm t] -> [MHDef t]
getDefs xs = [ def | (DefTm def _) <- xs ]

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
plus (Ab v (ItfMap m b) a) (Adj (ItfMap m' c) _) = Ab v (ItfMap (M.union m' m) b) a

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
