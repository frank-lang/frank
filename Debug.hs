{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module Debug where

import BwdFwd
import Syntax
import ParserCommon
import TypeCheckCommon

import qualified Data.Map.Strict as M
import Data.List

import Debug.Trace

import Data.IORef
import System.IO.Unsafe

import qualified Text.PrettyPrint as PP

-- Set by the main entry point if relevant flag detected.
-- 1) debugVerboseOn
-- 2) debugParserOn
-- 3) debugTypeCheckOn
debugMode :: IORef (Bool, Bool, Bool)
{-# NOINLINE debugMode #-}
debugMode = unsafePerformIO (newIORef (False, False, False))

-- Hack: Use () argument to prevent caching
getDebugMode :: () -> (Bool, Bool, Bool)
{-# NOINLINE getDebugMode #-}
getDebugMode () = unsafePerformIO (readIORef debugMode)

-- 1) Output full (untrimmed) ty var names
-- Hack: Use () argument to prevent caching
debugVerboseOn :: () -> Bool
debugVerboseOn () = case getDebugMode () of (b, _, _) -> b

-- 1) Output parsing process
-- Hack: Use () argument to prevent caching
debugParserOn :: () -> Bool
debugParserOn () = case getDebugMode () of (_, b, _) -> b

-- 1) Output type checking process
-- Hack: Use () argument to prevent caching
debugTypeCheckOn :: () -> Bool
debugTypeCheckOn () = case getDebugMode () of (_, _, b) -> b

ifDebugParserOnThen :: MonadicParsing m => m () -> m ()
ifDebugParserOnThen f = if debugParserOn () then f else return ()

ifDebugTypeCheckOnThen :: Contextual () -> Contextual ()
ifDebugTypeCheckOnThen f = if debugTypeCheckOn () then f else return ()

{- Error messages (only producing the output strings) -}

errorRefNoMainFunction :: String
errorRefNoMainFunction = "no main function defined"

errorRefDuplParamData :: DataT Raw -> String
errorRefDuplParamData dt@(DT x _ _ _) = "duplicate parameter in datatype " ++ x ++ " (" ++ (show $ ppHasSource dt) ++ ")"

errorRefDuplParamItf :: Itf Raw -> String
errorRefDuplParamItf itf@(Itf x _ _ _) = "duplicate parameter in interface " ++ x ++ " (" ++ (show $ ppHasSource itf) ++ ")"

errorRefDuplParamItfAl :: ItfAlias Raw -> String
errorRefDuplParamItfAl itfAl@(ItfAlias x _ _ _) = "duplicate parameter in interface alias " ++ x ++ " (" ++ (show $ ppHasSource itfAl) ++ ")"

errorRefDuplParamCmd :: Cmd Raw -> String
errorRefDuplParamCmd cmd@(Cmd x _ _ _ _) = "duplicate parameter in command " ++ x ++ " (" ++ (show $ ppHasSource cmd) ++ ")"

errorRefAbMultEffVars :: Ab Raw -> [Id] -> String
errorRefAbMultEffVars ab@(Ab v m a) es = "ability has multiple effect variables " ++ show es ++ " (" ++ (show $ ppHasSource ab) ++ ")"

errorRefEffVarNoParams :: Id -> [TyArg Raw] -> String
errorRefEffVarNoParams x tyArgs = "effect variable " ++ x ++ " may not take parameters"

errorRefIdNotDeclared :: String -> Id -> Raw -> String
errorRefIdNotDeclared sort x a = "no " ++ sort ++ " named " ++ x ++ " declared (" ++ (show $ ppHasSource a) ++ ")"

errorRefExpectedUse :: Tm Refined -> String
errorRefExpectedUse tm = "expected use but got term: " ++ show tm ++ "(" ++ (show $ ppHasSource tm) ++ ")"

errorRefEntryAlreadyDefined :: String -> Id -> String
errorRefEntryAlreadyDefined sort x = sort ++ " " ++ x ++ " already defined"

errorRefDuplTopTm :: String -> Id -> Raw -> String
errorRefDuplTopTm sort x a = "duplicate " ++ sort ++ ": " ++ x ++ " already defined (" ++ (show $ ppHasSource a) ++ ")"

errorRefNumberOfArguments :: Id -> Int -> Int -> Raw -> String
errorRefNumberOfArguments x exp act a = x ++ " expects " ++ show exp ++ " argument(s) but " ++ show act ++ " given (" ++ (show $ ppHasSource a) ++ ")"

errorRefItfAlCycle :: Id -> String
errorRefItfAlCycle x = "interface alias " ++ show x ++ " is defined in terms of itself (cycle)"

errorTCNotInScope :: Operator Desugared -> String
errorTCNotInScope op = "'" ++ getOpName op ++ "' not in scope (" ++ (show $ ppHasSource op) ++ ")"

errorTCPatternPortMismatch :: Clause Desugared -> String
errorTCPatternPortMismatch cls = "number of patterns not equal to number of ports (" ++ (show $ ppHasSource cls) ++ ")"

errorTCCmdNotFoundInAdj :: Id -> Adj Desugared -> String
errorTCCmdNotFoundInAdj cmd adj = "command " ++ cmd ++ " not found in adjustment " ++ (show $ ppAdj adj) ++ " (" ++ (show $ ppHasSource adj) ++ ")"

errorTCNotACtr :: Id -> String
errorTCNotACtr x = "'" ++ x ++ "' is not a constructor"

errorUnifDiffNumberArgs :: VType Desugared -> VType Desugared -> String
errorUnifDiffNumberArgs v1 v2 =
  "failed to unify " ++ (show $ ppVType v1) ++ " (" ++ (show $ ppHasSource v1) ++ ") with " ++ (show $ ppVType v2) ++ " (" ++ (show $ ppHasSource v2) ++ ")" ++ " because they have different numbers of type arguments"

errorUnifTys :: VType Desugared -> VType Desugared -> String
errorUnifTys t1 t2 =
  "failed to unify " ++ (show $ ppVType t1) ++ " (" ++ (show $ ppHasSource t1) ++ ") with " ++ (show $ ppVType t2) ++ " (" ++ (show $ ppHasSource t2) ++ ")"

errorUnifTyArgs :: TyArg Desugared -> TyArg Desugared -> String
errorUnifTyArgs t1 t2 =
  "failed to unify type arguments " ++ (show $ ppTyArg t1) ++ " (" ++ (show $ ppHasSource t1) ++ ")" ++ " with " ++ (show $ ppTyArg t2) ++ " (" ++ (show $ ppHasSource t2) ++ ")"

errorUnifAbs :: Ab Desugared -> Ab Desugared -> String
errorUnifAbs ab1 ab2 =
  "cannot unify abilities " ++ (show $ ppAb ab1) ++ " (" ++ (show $ ppHasSource ab1) ++ ")" ++ " and " ++ (show $ ppAb ab2) ++ " (" ++ (show $ ppHasSource ab2) ++ ")"

errorUnifItfMaps :: ItfMap Desugared -> ItfMap Desugared -> String
errorUnifItfMaps m1 m2 =
  "cannot unify interface maps " ++ (show $ ppItfMap m1) ++ " (" ++ (show $ ppHasSource m1) ++ ")" ++ " and " ++ (show $ ppItfMap m2) ++ " (" ++ (show $ ppHasSource m2) ++ ")"

errorUnifSolveOccurCheck :: String
errorUnifSolveOccurCheck = "solve: occurs check failure"

errorFindCmdNotPermit :: String -> Desugared -> String -> Ab Desugared -> String
errorFindCmdNotPermit cmd loc itf amb = "command " ++ cmd ++ " belonging to interface " ++ itf ++ " not permitted by ambient ability: " ++ (show $ ppAb amb) ++ " (" ++ (show $ ppHasSource amb) ++ ")"

{- Logging (output if debug mode is on) -}

logBeginFindCmd :: Id -> Id -> Maybe [TyArg Desugared] -> Contextual ()
logBeginFindCmd x itf mps = ifDebugTypeCheckOnThen $
  debugTypeCheckM $ "find command " ++ show x ++ " of interface " ++ show itf ++
                    " with instantiation " ++ show mps ++ "\n\n"

logEndFindCmd :: Id -> VType Desugared -> Contextual ()
logEndFindCmd x ty = ifDebugTypeCheckOnThen $
  debugTypeCheckM $ "ended find command " ++ show x ++ ", resulting type is: " ++
                    show (ppVType ty)

logBeginInferUse :: Use Desugared -> Contextual ()
logBeginInferUse (Op x _) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "begin infer use of single: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show x ++ "\n\n"
  ctx <- getContext
  debugTypeCheckM ("cur. context is:\n" ++ (show $ ppContext ctx) ++ "\n\n")
logBeginInferUse (App f xs _) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "begin infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show f ++ " " ++ show xs ++ "\n\n"

logEndInferUse :: Use Desugared -> VType Desugared -> Contextual ()
logEndInferUse (Op x _) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "ended infer use of single: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show x ++ "\n   gives " ++ show (ppVType ty)
  ctx <- getContext
  debugTypeCheckM ("cur. context is:\n" ++ (show $ ppContext ctx) ++ "\n\n")
logEndInferUse (App f xs _) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "ended infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show f ++ " " ++ show xs ++ "\n   gives " ++ show (ppVType ty) ++ "\n\n"

logBeginUnify :: VType Desugared -> VType Desugared -> Contextual ()
logBeginUnify t0 t1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "begin to unify\n   " ++ show (ppVType t0) ++ "\nwith\n   " ++ show (ppVType t1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

logEndUnify :: VType Desugared -> VType Desugared -> Contextual ()
logEndUnify t0 t1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "ended unifying\n   " ++ show (ppVType t0) ++ "\nwith\n   " ++ show (ppVType t1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

logBeginUnifyAb :: Ab Desugared -> Ab Desugared -> Contextual ()
logBeginUnifyAb ab0 ab1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "begin to unify ab. \n   " ++ show (ppAb ab0) ++ "\nwith\n   " ++ show (ppAb ab1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

logEndUnifyAb :: Ab Desugared -> Ab Desugared -> Contextual ()
logEndUnifyAb ab0 ab1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "ended unifying ab. \n   " ++ show (ppAb ab0) ++ "\nwith\n   " ++ show (ppAb ab1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

logBeginSolve :: Id -> Suffix -> VType Desugared -> Contextual ()
logBeginSolve a ext ty = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "begin to solve " ++ show a ++ " = " ++ show (ppVType ty) ++ "\n under suffix\n   " ++ show (ppSuffix ext) ++ "\n\n"

logSolveStep :: (Bool, Bool, Decl) -> Contextual ()
logSolveStep p = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "solving step: "
  case p of
    (_,     _,     TyDefn bty) -> debugTypeCheckM "\"inst-subs\""
    (True,  True,  Hole)       -> return ()
    (True,  False, Hole)       -> debugTypeCheckM "\"inst-define\""
    (False, True,  _)          -> debugTypeCheckM "\"inst-depend\""
    (False, False, d)          -> debugTypeCheckM $ "\"inst-skip-ty\", decl=" ++ show d
    (_,     _,     AbDefn _)   -> return ()
  debugTypeCheckM $ "current context:\n" ++ show (ppContext ctx) ++ "\n\n"

logEndSolve :: Id -> Suffix -> VType Desugared -> Contextual ()
logEndSolve a ext ty = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "ended solving " ++ show a ++ " = " ++ show (ppVType ty) ++ "\n under suffix\n   " ++ show (ppSuffix ext) ++ "\n\n"

-- Uses the hack of of first retrieving context but without printing it.
-- This achieves that calls of this function are not cached and newly executed
-- every time.
debugTypeCheckM :: String -> Contextual ()
debugTypeCheckM str = ifDebugTypeCheckOnThen $ do
  cxt <- getContext
  seq (ppContext cxt) traceM str

debugParserM :: (MonadicParsing m) => String -> m ()
debugParserM str = ifDebugParserOnThen $ do
  traceM str

{- Syntax pretty printers -}

(<+>) = (PP.<+>)
(<>) = (PP.<>)
($$) = (PP.$$)
text = PP.text
sep = PP.sep
nest = PP.nest
vcat = PP.vcat

type Doc = PP.Doc

ppProg :: (Show a, HasSource a) => Prog a -> Doc
ppProg (MkProg tts) = vcat (map ((text "" $$) . ppTopTm) tts)

ppTopTm :: (Show a, HasSource a) => TopTm a -> Doc
ppTopTm (DataTm dt _) = ppDataT dt
ppTopTm (ItfTm itf _) = text $ show itf
ppTopTm (SigTm sig _) = text $ show sig
ppTopTm (ClsTm cls _) = text $ show cls
ppTopTm (DefTm def _) = ppMHDef def

ppDataT :: (Show a, HasSource a) => DataT a -> Doc
ppDataT (DT id tyVars ctrs a) = text "data" <+>
                              text id <+>
                              sep (map (text . show) tyVars) <+>
                              text "=" <+>
                              sep (map (text . show) ctrs)

ppMHDef :: (Show a, HasSource a) => MHDef a -> Doc
ppMHDef (Def id cty cls _) = text id <+> text ":" <+>
                             ppCType cty $$
                             sep (map (ppClause id) cls)

ppClause :: (Show a, HasSource a) => Id -> Clause a -> Doc
ppClause id (Cls ps tm _) = text id <+>
                            (vcat . map ppPattern) ps <+> text "=" $$
                            (nest 3 . text . show) tm

ppPattern :: (Show a, HasSource a) => Pattern a -> Doc
ppPattern = text . show

ppCType :: (Show a, HasSource a) => CType a -> Doc
ppCType (CType ps q _) = text "{" <> ports <> peg <> text "}"
  where
    ports = case map ppPort ps of
      [] -> PP.empty
      xs -> foldl (\acc x -> x <+> text "-> " <> acc) PP.empty (reverse xs)
    peg = ppPeg q

ppVType :: (Show a, HasSource a) => VType a -> Doc
ppVType (DTTy x ts _) = text x <+> foldl (<+>) PP.empty (map ppTyArg ts)
ppVType (SCTy cty _) = ppCType cty
ppVType (TVar x _) = text x
ppVType (RTVar x _) = if debugVerboseOn () then text x else text $ trimVar x
ppVType (FTVar x _) = if debugVerboseOn () then text x else text $ trimVar x
ppVType (StringTy _) = text "String"
ppVType (IntTy _) = text "Int"
ppVType (CharTy _) = text "Char"

ppTyArg :: (Show a, HasSource a) => TyArg a -> Doc
ppTyArg (VArg t _) = ppParenVType t
ppTyArg (EArg ab _) = ppAb ab

ppParenVType :: (Show a, HasSource a) => VType a -> Doc
ppParenVType v@(DTTy _ _ _) = text "(" <+> ppVType v <+> text ")"
ppParenVType v = ppVType v

ppPort :: (Show a, HasSource a) => Port a -> Doc
ppPort (Port adj ty _) = ppAdj adj <> ppVType ty

ppPeg :: (Show a, HasSource a) => Peg a -> Doc
ppPeg (Peg ab ty _) = ppAb ab <> ppVType ty

ppAdj :: (Show a, HasSource a) => Adj a -> Doc
ppAdj (Adj (ItfMap m _) _) | M.null m = PP.empty
ppAdj (Adj m _) = text "<" <> ppItfMap m <> text ">"

ppAb :: (Show a, HasSource a) => Ab a -> Doc
ppAb (Ab v (ItfMap m _) _) | M.null m = text "[" <> ppAbMod v <> text "]"
ppAb (Ab v m _) =
  text "[" <> ppAbMod v <+> text "|" <+> ppItfMap m <> text "]"

ppAbMod :: (Show a, HasSource a) => AbMod a -> Doc
ppAbMod (EmpAb _) = text "0"
ppAbMod (AbVar x _) = text x
ppAbMod (AbRVar x _) = if debugVerboseOn () then text x else text $ trimVar x
ppAbMod (AbFVar x _) = if debugVerboseOn () then text x else text $ trimVar x

ppItfMap :: (Show a, HasSource a) => ItfMap a -> Doc
ppItfMap (ItfMap m _) = PP.hsep $ intersperse PP.comma $ map ppItfMapPair $ M.toList m
 where ppItfMapPair :: (Show a, HasSource a) => (Id, [TyArg a]) -> Doc
       ppItfMapPair (x, args) =
         text x <+> (foldl (<+>) PP.empty $ map ppTyArg args)

ppSource :: Source -> Doc
ppSource (InCode (line, col)) = text "line" <+> text (show line) <+> text ", column" <+> text (show col)
ppSource BuiltIn = text "built-in"
ppSource Implicit = text "implicit"
ppSource (ImplicitNear (line, col)) = text "implicit near line" <+> text (show line) <+> text ", column" <+> text (show col)
ppSource Generated = text "generated"


ppHasSource :: (HasSource a) => a -> Doc
ppHasSource x = ppSource (getSource x)

{- TypeCheckCommon pretty printers -}

ppContext :: Context -> Doc
ppContext = ppFwd . (map ppEntry) . bwd2fwd

ppEntry :: Entry -> Doc
ppEntry (FlexMVar x decl) = text "FlexMVar " <+> text x <+> text "\t=\t\t" <+> (ppDecl decl)
ppEntry (TermVar op ty)   = text "TermVar " <+> text (show op) <+> text "\t:=\t" <+> (ppVType ty)
ppEntry Mark              = text "<Mark>"

ppDecl :: Decl -> Doc
ppDecl Hole        = text "?"
ppDecl (TyDefn ty) = text "val.ty. " <+> ppVType ty
ppDecl (AbDefn ab) = text "eff.ty. " <+> ppAb ab

ppSuffix :: Suffix -> Doc
ppSuffix = ppFwd . (map (\(x, d) -> "(" ++ show x ++ "," ++ show (ppDecl d) ++ ")"))

{- BwdFwd pretty printers -}

ppFwd :: Show a => [a] -> Doc
ppFwd [] = text "[]"
ppFwd xs = text "[" $$
           sep (map ((nest 3) . text . show) xs) $$
           text "]"

ppBwd :: Show a => Bwd a -> Doc
ppBwd = ppFwd . bwd2fwd
