-- Specifies communication with user: Debugging, Error reporting, ...
{-# LANGUAGE GADTs #-}
module Debug where

import Prelude hiding ((<>))

import BwdFwd
import Syntax
import ParserCommon
import RefineSyntaxCommon
import TypeCheckCommon

import Control.Monad
import Control.Monad.Except
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List

import Debug.Trace

import Data.IORef
import System.IO.Unsafe

import Shonky.Syntax
import Shonky.Renaming

import qualified Text.PrettyPrint as PP

-- Is set by the main entry point if relevant flag detected.
-- 1) isDebugVerboseOn
-- 2) isDebugParserOn
-- 3) isDebugTypeCheckOn
debugMode :: IORef (Bool, Bool, Bool)
{-# NOINLINE debugMode #-}
debugMode = unsafePerformIO (newIORef (False, False, False))

-- Hack: Use () argument to prevent caching
getDebugMode :: () -> (Bool, Bool, Bool)
{-# NOINLINE getDebugMode #-}
getDebugMode () = unsafePerformIO (readIORef debugMode)

-- Output full (untrimmed) ty var names
-- Hack: Use () argument to prevent caching
isDebugVerboseOn :: () -> Bool
isDebugVerboseOn () = case getDebugMode () of (b, _, _) -> b

-- Output parsing process
-- Hack: Use () argument to prevent caching
isDebugParserOn :: () -> Bool
isDebugParserOn () = case getDebugMode () of (_, b, _) -> b

-- Output type checking process
-- Hack: Use () argument to prevent caching
isDebugTypeCheckOn :: () -> Bool
isDebugTypeCheckOn () = case getDebugMode () of (_, _, b) -> b

ifDebugTypeCheckOnThen :: Contextual () -> Contextual ()
ifDebugTypeCheckOnThen f = when (isDebugTypeCheckOn ()) f

{- Error messages (only producing the output strings) -}

errorRefNoMainFunction :: String
errorRefNoMainFunction = "no main function defined"

errorRefDuplParamData :: DataT Raw -> String
errorRefDuplParamData dt@(DT x _ _ _) = "duplicate parameter in datatype " ++ x ++ " (" ++ (show $ ppSourceOf dt) ++ ")"

errorRefDuplParamItf :: Itf Raw -> String
errorRefDuplParamItf itf@(Itf x _ _ _) = "duplicate parameter in interface " ++ x ++ " (" ++ (show $ ppSourceOf itf) ++ ")"

errorRefDuplParamItfAl :: ItfAlias Raw -> String
errorRefDuplParamItfAl itfAl@(ItfAlias x _ _ _) = "duplicate parameter in interface alias " ++ x ++ " (" ++ (show $ ppSourceOf itfAl) ++ ")"

errorRefDuplParamCmd :: Cmd Raw -> String
errorRefDuplParamCmd cmd@(Cmd x _ _ _ _) = "duplicate parameter in command " ++ x ++ " (" ++ (show $ ppSourceOf cmd) ++ ")"

errorRefAbMultEffVars :: Ab Raw -> [Id] -> String
errorRefAbMultEffVars ab@(Ab v m a) es = "ability has multiple effect variables " ++ show es ++ " (" ++ (show $ ppSourceOf ab) ++ ")"

errorRefEffVarNoParams :: Id -> String
errorRefEffVarNoParams x = "effect variable " ++ x ++ " may not take parameters"

errorRefIdNotDeclared :: String -> Id -> Raw -> String
errorRefIdNotDeclared sort x a = "no " ++ sort ++ " named " ++ x ++ " declared (" ++ (show $ ppSourceOf a) ++ ")"

errorRefExpectedUse :: Tm Refined -> String
errorRefExpectedUse tm = "expected use but got term: " ++ show tm ++ "(" ++ (show $ ppSourceOf tm) ++ ")"

errorRefEntryAlreadyDefined :: String -> Id -> String
errorRefEntryAlreadyDefined sort x = sort ++ " " ++ x ++ " already defined"

errorRefDuplTopTm :: String -> Id -> Source -> String
errorRefDuplTopTm sort x a = "duplicate " ++ sort ++ ": " ++ x ++ " already defined (" ++ show a ++ ")"

errorNumberOfArguments :: HasSource a => Id -> Int -> Int -> a -> String
errorNumberOfArguments x exp act a =
  x ++ " expects " ++ show exp ++ " argument(s) but " ++ show act ++
  " given (" ++ (show $ ppSourceOf a) ++ ")"

errorRefItfAlCycle :: Id -> String
errorRefItfAlCycle x = "interface alias " ++ show x ++ " is defined in terms of itself (cycle)"

errorTCNotInScope :: Operator Desugared -> String
errorTCNotInScope op = "'" ++ getOpName op ++ "' not in scope (" ++ (show $ ppSourceOf op) ++ ")"

errorTCPatternPortMismatch :: Clause Desugared -> String
errorTCPatternPortMismatch cls = "number of patterns not equal to number of ports (" ++ (show $ ppSourceOf cls) ++ ")"

errorTCCmdNotFoundInPort :: Id -> Int -> Port Desugared -> String
errorTCCmdNotFoundInPort cmd n port = "command " ++ cmd ++ "." ++ show n ++ " not found in adjustments of port " ++ (show $ ppPort port) ++ " (" ++ (show $ ppSourceOf port) ++ ")"

errorTCNotACtr :: Id -> String
errorTCNotACtr x = "'" ++ x ++ "' is not a constructor"

errorUnifDiffNumberArgs :: VType Desugared -> VType Desugared -> String
errorUnifDiffNumberArgs v1 v2 =
  "failed to unify " ++ (show $ ppVType v1) ++ " (" ++ (show $ ppSourceOf v1) ++ ") with " ++ (show $ ppVType v2) ++ " (" ++ (show $ ppSourceOf v2) ++ ")" ++ " because they have different numbers of type arguments"

errorUnifTys :: VType Desugared -> VType Desugared -> String
errorUnifTys t1 t2 =
  "failed to unify " ++ (show $ ppVType t1) ++ " (" ++ (show $ ppSourceOf t1) ++ ") with " ++ (show $ ppVType t2) ++ " (" ++ (show $ ppSourceOf t2) ++ ")"

errorUnifTyArgs :: TyArg Desugared -> TyArg Desugared -> String
errorUnifTyArgs t1 t2 =
  "failed to unify type arguments " ++ (show $ ppTyArg t1) ++ " (" ++ (show $ ppSourceOf t1) ++ ")" ++ " with " ++ (show $ ppTyArg t2) ++ " (" ++ (show $ ppSourceOf t2) ++ ")"

errorUnifAbs :: Ab Desugared -> Ab Desugared -> String
errorUnifAbs ab1 ab2 =
  "cannot unify abilities " ++ (show $ ppAb ab1) ++ " (" ++ (show $ ppSourceOf ab1) ++ ")" ++ " and " ++ (show $ ppAb ab2) ++ " (" ++ (show $ ppSourceOf ab2) ++ ")"

errorUnifItfMaps :: ItfMap Desugared -> ItfMap Desugared -> String
errorUnifItfMaps m1 m2 =
  "cannot unify interface maps " ++ (show $ ppItfMap m1) ++ " (" ++ (show $ ppSourceOf m1) ++ ")" ++ " and " ++ (show $ ppItfMap m2) ++ " (" ++ (show $ ppSourceOf m2) ++ ")"

errorAdaptor :: Adaptor Desugared -> Ab Desugared -> String
errorAdaptor adpd@(Adp x ns k _) ab =
  "Adaptor " ++ (show $ ppAdaptor adpd) ++
  " is not a valid adaptor in ambient " ++ (show $ ppAb ab) ++
  " (" ++  (show $ ppSourceOf adpd) ++ ")"
errorAdaptor adpd@(CompilableAdp x m ns _) ab =
  "Adaptor " ++ (show $ ppAdaptor adpd) ++
  " is not a valid adaptor in ambient " ++ (show $ ppAb ab) ++
  " (" ++  (show $ ppSourceOf adpd) ++ ")"

errorUnifSolveOccurCheck :: String
errorUnifSolveOccurCheck = "solve: occurs check failure"

errorFindCmdNotPermit :: String -> Desugared -> String -> Ab Desugared -> String
errorFindCmdNotPermit cmd loc itf amb = "command " ++ cmd ++ " belonging to interface " ++ itf ++ " not permitted by ambient ability: " ++ (show $ ppAb amb) ++ " (" ++ (show $ ppSourceOf amb) ++ ")"

{- Logging (output if debug mode is on) -}

logBeginFindCmd :: Id -> Id -> Maybe [TyArg Desugared] -> Contextual ()
logBeginFindCmd x itf mps = ifDebugTypeCheckOnThen $
  debugTypeCheckM $ "find command " ++ show x ++ " of interface " ++ show itf ++
                    " with instantiation " ++ show (mps >>= Just . (map (show . ppTyArg))) ++ "\n\n"

logEndFindCmd :: Id -> VType Desugared -> Contextual ()
logEndFindCmd x ty = ifDebugTypeCheckOnThen $
  debugTypeCheckM $ "ended find command " ++ show x ++ ", resulting type is: " ++
                    show (ppVType ty)

logBeginInferUse :: Use Desugared -> Contextual ()
logBeginInferUse u@(Op x _) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "begin infer use of single: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n\n"
  ctx <- getContext
  debugTypeCheckM ("cur. context is:\n" ++ (show $ ppContext ctx) ++ "\n\n")
logBeginInferUse u@(App f xs _) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "begin infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n\n"
logBeginInferUse u@(Adapted rs t _) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "begin infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n\n"


logEndInferUse :: Use Desugared -> VType Desugared -> Contextual ()
logEndInferUse u@(Op x _) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "ended infer use of single: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n   gives " ++ show (ppVType ty)
  ctx <- getContext
  debugTypeCheckM ("cur. context is:\n" ++ (show $ ppContext ctx) ++ "\n\n")
logEndInferUse u@(App f xs _) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "ended infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n   gives " ++ show (ppVType ty) ++ "\n\n"
logEndInferUse u@(Adapted rs t _) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "ended infer use of redirected: Under curr. amb. " ++
    show (ppAb amb) ++ " redirected by <" ++ (show rs) ++
    ">\n   infer type of " ++ show (ppUse u) ++
    "\n   gives " ++ show (ppVType ty) ++ "\n\n"

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

-- logBeginSolveForEVar :: Id -> Suffix -> VType Desugared -> Contextual ()
-- logBeginSolve a ext ty = ifDebugTypeCheckOnThen $ do
--   ctx <- getContext
--   debugTypeCheckM $ "begin to solve " ++ show a ++ " = " ++ show (ppVType ty) ++ "\n under suffix\n   " ++ show (ppSuffix ext) ++ "\n\n"
--
-- logEndSolveForEVar :: Id -> Suffix -> VType Desugared -> Contextual ()
-- logEndSolve a ext ty = ifDebugTypeCheckOnThen $ do
--   ctx <- getContext
--   debugTypeCheckM $ "ended solving " ++ show a ++ " = " ++ show (ppVType ty) ++ "\n under suffix\n   " ++ show (ppSuffix ext) ++ "\n\n"

debugParserM :: (MonadicParsing m) => String -> m ()
debugParserM = traceM

debugRefineM :: String -> Refine ()
debugRefineM = traceM

checkArgs :: Id -> Int -> Int -> Raw -> Refine ()
checkArgs x exp act a =
  when (exp /= act) $
    throwError $ errorNumberOfArguments x exp act a

debugRefine :: String -> a -> a
debugRefine = trace

-- Uses the hack of of first retrieving context but without printing it.
-- This achieves that calls of this function are not cached and newly executed
-- every time.
debugTypeCheckM :: String -> Contextual ()
debugTypeCheckM str = do
  cxt <- getContext
  seq (ppContext cxt) traceM str

debugM :: (Monad m) => String -> m ()
debugM = traceM

{- Syntax pretty printers -}

(<+>) = (PP.<+>)
(<>) = (PP.<>)
($$) = (PP.$$)
($+$) = (PP.$+$)
text = PP.text
sep = PP.sep
nest = PP.nest
vcat = PP.vcat
hcat = PP.hcat
hsep = PP.hsep
colon = PP.colon
comma = PP.comma
empty = PP.empty
int = PP.int
punctuate = PP.punctuate
semi = PP.semi
rbrack = PP.rbrack
lbrack = PP.lbrack
doubleQuotes = PP.doubleQuotes
ppBrackets = PP.brackets
ppParens = PP.parens
ppChar = PP.char
vsep :: [PP.Doc] -> PP.Doc
vsep = foldr ($+$) empty

type Doc = PP.Doc

ppProg :: (Show a, HasSource a) => Prog a -> PP.Doc
ppProg (MkProg tts) = foldl (PP.$+$ ) PP.empty (map ppTopTm tts)

ppTopTm :: (Show a, HasSource a) => TopTm a -> PP.Doc
ppTopTm (DataTm dt _) = ppDataT dt
ppTopTm (ItfTm itf _) = ppItf itf
ppTopTm (SigTm sig _) = text $ show sig
ppTopTm (ClsTm cls _) = text $ show cls
ppTopTm (DefTm def _) = ppMHDef def

ppDataT :: (Show a, HasSource a) => DataT a -> PP.Doc
ppDataT (DT id tyVars ctrs a) = text "data" <+>
                              text id <+>
                              sep (map (text . show) tyVars) <+>
                              text "=" <+>
                              sep (map (text . show) ctrs)

ppItf :: (Show a, HasSource a) => Itf a -> PP.Doc
ppItf (Itf id tyVars cmds a) = text "interface" <+>
                           text id <+>
                           sep (map (text . show) tyVars) <+>
                           text "=" <+>
                           sep (map (text . show) cmds)

ppMHDef :: (Show a, HasSource a) => MHDef a -> PP.Doc
ppMHDef (Def id cty cls _) = text id <+> text ":" <+>
                             ppCType cty $$
                             sep (map (ppClause id) cls)

ppClause :: (Show a, HasSource a) => Id -> Clause a -> PP.Doc
ppClause id (Cls ps tm _) = text id <+>
                            (vcat . map ppPattern) ps <+> text "=" $$
                            (nest 3 . ppTm) tm

ppPattern :: (Show a, HasSource a) => Pattern a -> PP.Doc
ppPattern (VPat vp _) = ppValuePat vp
ppPattern (CmdPat x n vps k _) = text "<" <+>
                                 text x <>
                                 (if n == 0 then empty
                                            else text "." <> int n) <+>
                                 (hcat . map ppValuePat) vps <+>
                                 text "->" <+>
                                 text k <+>
                                 text ">"
ppPattern (ThkPat x _) = text x

ppValuePat :: (Show a, HasSource a) => ValuePat a -> PP.Doc
ppValuePat (VarPat x _) = text x
ppValuePat (DataPat x vps _) = text x <+> (hcat . map ppValuePat) vps
ppValuePat (IntPat n _) = (text . show) n
ppValuePat (CharPat c _) = (text . show) c
ppValuePat (StrPat s _) = (text . show) s
ppValuePat (ConsPat vp1 vp2 _) = ppValuePat vp1 <+> text "::" <+> ppValuePat vp2
ppValuePat (ListPat vps _) = (hcat . map ppValuePat) vps

ppCType :: (Show a, HasSource a) => CType a -> PP.Doc
ppCType (CType ps q _) = text "{" <> ports <> peg <> text "}"
  where
    ports = case map ppPort ps of
      [] -> PP.empty
      xs -> foldl (\acc x -> x <+> text "-> " <> acc) PP.empty (reverse xs)
    peg = ppPeg q

ppVType :: (Show a, HasSource a) => VType a -> PP.Doc
ppVType (DTTy x ts _) = text x <+> foldl (<+>) PP.empty (map ppTyArg ts)
ppVType (SCTy cty _) = ppCType cty
ppVType (TVar x _) = text x
ppVType (RTVar x _) = if isDebugVerboseOn () then text x else text $ trimVar x
ppVType (FTVar x _) = if isDebugVerboseOn () then text x else text $ trimVar x
ppVType (StringTy _) = text "String"
ppVType (IntTy _) = text "Int"
ppVType (CharTy _) = text "Char"

ppTyArg :: (Show a, HasSource a) => TyArg a -> PP.Doc
ppTyArg (VArg t _) = ppParenVType t
ppTyArg (EArg ab _) = ppAb ab

ppParenVType :: (Show a, HasSource a) => VType a -> PP.Doc
ppParenVType v@(DTTy _ _ _) = text "(" <+> ppVType v <+> text ")"
ppParenVType v = ppVType v

ppPort :: (Show a, HasSource a) => Port a -> PP.Doc
ppPort (Port []   ty _) = ppVType ty
ppPort (Port adjs ty _) = text "<" <> (PP.hsep $ intersperse PP.comma $ map ppAdj adjs) <> text ">" <> ppVType ty

ppPeg :: (Show a, HasSource a) => Peg a -> PP.Doc
ppPeg (Peg ab ty _) = ppAb ab <> ppVType ty

ppAdj :: (Show a, HasSource a) => Adjustment a -> PP.Doc
ppAdj (ConsAdj x ts _) = ppItfInstance (x, ts)
ppAdj (AdaptorAdj adp _) = ppAdaptor adp

ppAb :: (Show a, HasSource a) => Ab a -> PP.Doc
ppAb (Ab v (ItfMap m _) _) | M.null m = text "[" <> ppAbMod v <> text "]"
ppAb (Ab v m _) =
  text "[" <> ppAbMod v <+> text "|" <+> ppItfMap m <> text "]"

ppAbMod :: (Show a, HasSource a) => AbMod a -> PP.Doc
ppAbMod (EmpAb _) = text "0"
ppAbMod (AbVar x _) = text x
ppAbMod (AbRVar x _) = if isDebugVerboseOn () then text x else text $ trimVar x
ppAbMod (AbFVar x _) = if isDebugVerboseOn () then text x else text $ trimVar x

ppItfMap :: (Show a, HasSource a) => ItfMap a -> PP.Doc
ppItfMap (ItfMap m _) =
  PP.hsep $ intersperse PP.comma $ map ppItfInstances $ M.toList m

ppItfInstances :: (Show a, HasSource a) => (Id, Bwd [TyArg a]) -> PP.Doc
ppItfInstances (x, instants) =
        PP.hsep $ intersperse PP.comma $ map (\args -> foldl (<+>) (text x) $ map ppTyArg args) (bwd2fwd instants)

ppItfInstance :: (Show a, HasSource a) => (Id, [TyArg a]) -> PP.Doc
ppItfInstance (x, ts) = text x <+> (PP.hsep $ map ppTyArg ts)

ppSource :: Source -> PP.Doc
ppSource (InCode (line, col)) = text "line" <+> text (show line) <+> text ", column" <+> text (show col)
ppSource BuiltIn = text "built-in"
ppSource Implicit = text "implicit"
ppSource (ImplicitNear (line, col)) = text "implicit near line" <+> text (show line) <+> text ", column" <+> text (show col)
ppSource Generated = text "generated"


ppSourceOf :: (HasSource a) => a -> PP.Doc
ppSourceOf x = ppSource (getSource x)

ppTm :: (Show a, HasSource a) => Tm a -> PP.Doc
ppTm (SC sc _) = ppSComp sc
ppTm (StrTm str _) = text "{" <+> text str <+> text "}"
ppTm (IntTm n _) = text (show n)
ppTm (CharTm c _) = text (show c)
ppTm (ListTm xs _) = text "[" <+> sep (map ppTm xs) <+> text "]"
ppTm (TmSeq t1 t2 _) = PP.parens $ ppTm t1 <+> text "; " <+> ppTm t2
ppTm (Use u _) = PP.parens $ ppUse u
ppTm (DCon dc _) = PP.parens $ ppDataCon dc

ppSComp :: (Show a, HasSource a) => SComp a -> PP.Doc
ppSComp (SComp cls _) = text "{" <+> sep (map (ppClause "") cls) <+> text "}"

ppUse :: (Show a, HasSource a) => Use a -> PP.Doc
ppUse (RawId x _) = text x
ppUse (RawComb u args _) = PP.lparen <> ppUse u <+> ppArgs args <> PP.rparen
ppUse (Op op _) = ppOperator op
ppUse (App u args _) = PP.lparen <> ppUse u <+> ppArgs args <> PP.rparen
ppUse (Adapted rs t _) =
  PP.parens $ text "<" <> ppAdaptors rs <> text ">" <+> ppUse t

-- TODO: LC: fix parenthesis output...
ppArgs :: (Show a, HasSource a) => [Tm a] -> PP.Doc
ppArgs [] = text "!"
ppArgs args = sep (map ppTm args)

ppOperator :: (Show a, HasSource a) => Operator a -> PP.Doc
ppOperator (Mono x _) = text x
ppOperator (Poly x _) = text x
ppOperator (VarId x _) = text x
ppOperator (CmdId x _) = text x

ppDataCon :: (Show a, HasSource a) => DataCon a -> PP.Doc
ppDataCon (DataCon x tms _) = text x <+> sep (map ppTm tms)

ppAdaptors :: (Show a, HasSource a) => [Adaptor a] -> PP.Doc
ppAdaptors rs = PP.hsep $ intersperse PP.comma $ map ppAdaptor rs

ppAdaptor :: (Show a, HasSource a) => Adaptor a -> PP.Doc
ppAdaptor (RawAdp x liat left right _) =
  text x <> text "(" <> text (show liat) <+> sep (punctuate (text " ") (map (text . show) left)) <+> text "->" <+> sep (punctuate (text " ") (map (text . show) right)) <> text ")"
ppAdaptor (Adp x mm ns _) =
  text x <> text "(" <> text (show mm) <> comma <+> sep (punctuate comma (map int ns)) <> text ")"
ppAdaptor (CompilableAdp x m ns _) =
  text x <> text "(" <> sep (punctuate comma (map int ns)) <> text ")(" <>
  int m <> text ")"

{- TypeCheckCommon pretty printers -}

ppContext :: Context -> PP.Doc
ppContext = ppFwd . (map ppEntry) . bwd2fwd

ppEntry :: Entry -> PP.Doc
ppEntry (FlexMVar x decl) = text "FlexMVar " <+> text x <+> text "\t=\t\t" <+> (ppDecl decl)
ppEntry (TermVar op ty)   = text "TermVar " <+> text (show op) <+> text "\t:=\t" <+> (ppVType ty)
ppEntry Mark              = text "<Mark>"

ppDecl :: Decl -> PP.Doc
ppDecl Hole        = text "?"
ppDecl (TyDefn ty) = text "val.ty. " <+> ppVType ty
ppDecl (AbDefn ab) = text "eff.ty. " <+> ppAb ab

ppSuffix :: Suffix -> PP.Doc
ppSuffix = ppFwd . (map (\(x, d) -> "(" ++ show x ++ "," ++
                                    show (ppDecl d) ++ ")"))

ppItfs :: [Id] -> PP.Doc
ppItfs p = PP.hsep $ intersperse PP.comma $ map text p

{- BWDFWD pretty printers -}

ppFwd :: Show a => [a] -> PP.Doc
ppFwd [] = text "[]"
ppFwd xs = text "[" $$
           sep (map ((nest 3) . text . show) xs) $$
           text "]"

ppBwd :: Show a => Bwd a -> PP.Doc
ppBwd = ppFwd . bwd2fwd

{- Shonky pretty printers -}

-- Pretty printing routines

ppProgShonky :: [Def Exp] -> PP.Doc
ppProgShonky xs = vcat (punctuate (text "\n") (map ppDef xs))

ppDef :: Def Exp -> PP.Doc
ppDef (id := e) = text id <+> text "->" <+> ppExp e
ppDef (DF id [] []) = error "ppDef invariant broken: empty Def Exp detected."
ppDef p@(DF id hss es) = header $+$ vcat cs
  where header = text id <> PP.parens (hsep portAnnots) <> colon
        portAnnots = punctuate comma $ map ppPort hss
        cs = punctuate comma $
               map (\x -> text id <> (nest 3 (ppClauseShonky ($$) x))) es
        ppPort :: ([Adap], [String]) -> PP.Doc
        ppPort (adps, cmds) = PP.parens ((hsep $ punctuate comma (map ppAdap adps))
                            <+> comma <+> (hsep $ punctuate comma (map text cmds)))
        ppAdap :: Adap -> PP.Doc
        ppAdap (cmds, r) = text "([" <> (hsep $ punctuate comma (map text cmds)) <> text "]" <+>
                           comma <+> ppRenaming r <+> text ")"
-- TODO: LC: refactor above pretty-printer

ppText :: (a -> PP.Doc) -> [Either Char a] -> PP.Doc
ppText f ((Left c) : xs) = (text $ escChar c) <> (ppText f xs)
ppText f ((Right x) : xs) = text "`" <> f x <> text "`" <> (ppText f xs)
ppText f [] = text "|]"

isEscChar :: Char -> Bool
isEscChar c = any (c ==) ['\n','\t','\b']

escChar :: Char -> String
escChar c = f [('\n', "\\n"),('\t', "\\t"),('\b', "\\b")]
  where f ((c',s):xs) = if c == c' then s else f xs
        f [] = [c]

ppClauseShonky :: (PP.Doc -> PP.Doc -> PP.Doc) -> ([Pat], Exp) -> PP.Doc
ppClauseShonky comb (ps, e) =
  let rhs = PP.parens (hsep $ punctuate comma (map ppPat ps))
      lhs = ppExp e in
  rhs <+> text "->" `comb` lhs

ppExp :: Exp -> PP.Doc
ppExp (EV x) = text x
ppExp (EI n) = int n
ppExp (EA x) = text $ "'" ++ x
ppExp (e :& e') | isListExp e = text "[" <> ppListExp e'
ppExp p@(_ :& _) = text "[" <> ppExp' p
ppExp (f :$ xs) = let args = hcat $ punctuate comma (map ppExp xs) in
  ppExp f <> text "(" <> args <> text ")"
ppExp (e :! e') = ppExp e <> semi <> ppExp e'
ppExp (e :// e') = ppExp e <> text "/" <> ppExp e'
ppExp (EF xs ys) =
-- TODO: LC: Print xs
  let clauses = map (ppClauseShonky (<+>)) ys in
  PP.braces $ hcat (punctuate comma clauses)
ppExp (EX xs) = text "[|" <> ppText ppExp xs
ppExp (ER (cs, r) e) = text "<(" <+> (hcat $ punctuate comma (map text cs))
                    <> text ")" <+> ppRenaming r <> text ">"
                    <+> PP.parens (ppExp e)

ppExp' :: Exp -> PP.Doc
ppExp' (e :& EA "") = ppExp e <> rbrack
ppExp' (e :& es) = ppExp e <> comma <> ppExp' es
ppExp' e = ppExp e

isListExp :: Exp -> Bool
isListExp (e :& _) = isListExp e
isListExp _ = False

-- Special case for lists
ppListExp :: Exp -> PP.Doc
ppListExp (e :& EA "") = ppExp e <> text "]"
ppListExp (e :& es) = ppExp e <> text "|" <> ppListExp es
ppListExp (EA "") = text "]"
ppListExp _ = text "ppListExp: invariant broken"

ppPat :: Pat -> PP.Doc
ppPat (PV x) = ppVPat x
ppPat (PT x) = PP.braces $ text x
ppPat (PC cmd n ps k) = let args = hcat $ punctuate comma (map ppVPat ps) in
  let cmdtxt = text (cmd ++ ".") <> int n in
  PP.braces $ text "'" <> cmdtxt <> PP.parens args <+> text "->" <+> text k

ppVPat :: VPat -> PP.Doc
ppVPat (VPV x) = text x
ppVPat (VPI n) = int n
ppVPat (VPA x) = text $ "'" ++ x
ppVPat (VPX xs) = text "[|" <> ppText ppVPat xs
ppVPat (v1 :&: v2 :&: v3) = ppVPat (v1 :&: (v2 :&: v3))
ppVPat (v :&: v') | isListPat v = lbrack <> ppVPatList v'
ppVPat p@(_ :&: _) = lbrack <> ppVPat' p

ppVPatList :: VPat -> PP.Doc
ppVPatList (v :&: VPA "") = ppVPat v <> rbrack
ppVPatList (v :&: vs) = ppVPat v <> text "|" <> ppVPatList vs
ppVPatList (VPA "") = lbrack
ppVPatList _ = error "ppVPatList: broken invariant"

ppVPat' :: VPat -> PP.Doc
ppVPat' (v :&: VPA "") = ppVPat v <> text "]"
ppVPat' (v :&: vs) = ppVPat v <> comma <> ppVPat' vs
ppVPat' v = ppVPat v

isListPat :: VPat -> Bool
isListPat (v :&: _) = isListPat v
isListPat _ = False
