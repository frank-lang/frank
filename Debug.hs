{-# LANGUAGE GADTs #-}
module Debug where

import BwdFwd
import Syntax
import TypeCheckCommon

import qualified Data.Map.Strict as M
import Data.List

import Debug.Trace

import Data.IORef
import System.IO.Unsafe

import qualified Text.PrettyPrint as PP

-- Set by the main entry point if relevant flag detected.
-- 1) debugVerboseOn
-- 2) debugTypeCheckOn
debugMode :: IORef (Bool, Bool)
{-# NOINLINE debugMode #-}
debugMode = unsafePerformIO (newIORef (False, False))

getDebugMode :: () -> (Bool, Bool)
{-# NOINLINE getDebugMode #-}
getDebugMode () = unsafePerformIO (readIORef debugMode)

-- 1) Output full (untrimmed) ty var names
debugVerboseOn :: () -> Bool
debugVerboseOn () = fst $ getDebugMode ()

-- 1) Output type checking process
debugTypeCheckOn :: () -> Bool
debugTypeCheckOn () = snd $ getDebugMode ()

ifDebugTypeCheckOnThen :: Contextual () -> Contextual ()
ifDebugTypeCheckOnThen f = if debugTypeCheckOn () then f else return ()

{- Logging (output if debug mode is on) -}

logBeginFindCmd :: Id -> Id -> Maybe [TyArg Desugared] -> Contextual ()
logBeginFindCmd x itf mps = ifDebugTypeCheckOnThen $
  traceM $ "find command " ++ show x ++ " of interface " ++ show itf ++
           " with instantiation " ++ show mps ++ "\n\n"

logEndFindCmd :: Id -> VType Desugared -> Contextual ()
logEndFindCmd x ty = ifDebugTypeCheckOnThen $
  traceM $ "ended find command " ++ show x ++ ", resulting type is: " ++
           show (ppVType ty)

logBeginInferUse :: Use Desugared -> Contextual ()
logBeginInferUse (MkOp x) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  traceM $ "begin infer use of single: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show x ++ "\n\n"
logBeginInferUse (MkApp f xs) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  traceM $ "begin infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show f ++ " " ++ show xs ++ "\n\n"

logEndInferUse :: Use Desugared -> VType Desugared -> Contextual ()
logEndInferUse (MkOp x) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  traceM $ "ended infer use of single: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show x ++ "\n   gives " ++ show (ppVType ty) ++ "\n\n"
logEndInferUse (MkApp f xs) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  traceM $ "ended infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show f ++ " " ++ show xs ++ "\n   gives " ++ show (ppVType ty) ++ "\n\n"

logBeginUnifyAb :: Ab Desugared -> Ab Desugared -> Contextual ()
logBeginUnifyAb ab0 ab1 = ifDebugTypeCheckOnThen $ do
  traceM $ "begin to unify\n   " ++ show (ppAb ab0) ++ "\nwith\n   " ++ show (ppAb ab1) ++ "\n\n"

logEndUnifyAb :: Ab Desugared -> Ab Desugared -> Contextual ()
logEndUnifyAb ab0 ab1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  traceM $ "ended unifying\n   " ++ show (ppAb ab0) ++ "\nwith\n   " ++ show (ppAb ab1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

{- Syntax pretty printers -}

(<+>) = (PP.<+>)
(<>) = (PP.<>)
($$) = (PP.$$)
text = PP.text
sep = PP.sep
nest = PP.nest
vcat = PP.vcat

type Doc = PP.Doc

ppProg :: Prog a -> Doc
ppProg (MkProg tts) = vcat (map ((text "" $$) . ppTopTm) tts)

ppTopTm :: TopTm a -> Doc
ppTopTm (MkDataTm dt) = ppDataT dt
ppTopTm (MkItfTm itf) = text $ show itf
ppTopTm (MkSigTm sig) = text $ show sig
ppTopTm (MkClsTm cls) = text $ show cls
ppTopTm (MkDefTm def) = ppMHDef def

ppDataT :: DataT a -> Doc
ppDataT (MkDT id ty_vars ctrs) = text "data" <+>
                                 text id <+>
                                 sep (map (text . show) ty_vars) <+>
                                 text "=" <+>
                                 sep (map (text . show) ctrs)

ppMHDef :: MHDef a -> Doc
ppMHDef (MkDef id cty cls) = text id <+> text ":" <+>
                             ppCType cty $$
                             sep (map (ppClause id) cls)

ppClause :: Id -> Clause a -> Doc
ppClause id (MkCls ps tm) = text id <+>
                            (vcat . map ppPattern) ps <+> text "=" $$
                            (nest 3 . text . show) tm

ppPattern :: Pattern a -> Doc
ppPattern = text . show

ppCType :: CType a -> Doc
ppCType (MkCType ps q) = text "{" <> ports <> peg <> text "}"
  where
    ports = case map ppPort ps of
      [] -> PP.empty
      xs -> foldl (\acc x -> x <+> text "-> " <> acc) PP.empty (reverse xs)

    peg = ppPeg q

ppVType :: VType a -> Doc
ppVType (MkDTTy x ts) = text x <+> foldl (<+>) PP.empty (map ppTyArg ts)
ppVType (MkSCTy cty) = ppCType cty
ppVType (MkTVar x) = text x
ppVType (MkRTVar x) = if debugVerboseOn () then text x else text $ trimVar x
ppVType (MkFTVar x) = if debugVerboseOn () then text x else text $ trimVar x
ppVType MkStringTy = text "String"
ppVType MkIntTy = text "Int"
ppVType MkCharTy = text "Char"

ppTyArg :: TyArg a -> Doc
ppTyArg (VArg t) = ppParenVType t
ppTyArg (EArg ab) = ppAb ab

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
  text "[" <> ppAbMod v <+> text "|" <+> ppItfMap m <> text "]"

ppAbMod :: AbMod a -> Doc
ppAbMod MkEmpAb = text "0"
ppAbMod (MkAbVar x) = text x
ppAbMod (MkAbRVar x) = if debugVerboseOn () then text x else text $ trimVar x
ppAbMod (MkAbFVar x) = if debugVerboseOn () then text x else text $ trimVar x

ppItfMap :: ItfMap a -> Doc
ppItfMap m = PP.hsep $ intersperse PP.comma $ map ppItfMapPair $ M.toList m
 where ppItfMapPair :: (Id, [TyArg a]) -> Doc
       ppItfMapPair (x, args) =
         text x <+> (foldl (<+>) PP.empty $ map ppTyArg args)

{- TypeCheckCommon pretty printers -}

ppContext :: Context -> Doc
ppContext = ppFwd . (map ppEntry) . bwd2fwd

ppEntry :: Entry -> Doc
ppEntry (FlexMVar x decl) = text "FlexMVar " <+> text x <+> text " = "$$
                            nest 6 (ppDecl decl)
ppEntry (TermVar op ty)   = text "TermVar " <+> text (show op) <+> text " := " $$
                            nest 6 (ppVType ty)
ppEntry Mark              = text "<Mark>"


ppDecl :: Decl -> Doc
ppDecl Hole        = text "?"
ppDecl (TyDefn ty) = text "val.ty. " <+> ppVType ty
ppDecl (AbDefn ab) = text "eff.ty. " <+> ppAb ab

{- BwdFwd pretty printers -}

ppFwd :: Show a => [a] -> Doc
ppFwd [] = text "[]"
ppFwd xs = text "[" $$
           sep (map ((nest 3) . text . show) xs) $$
           text "]"

ppBwd :: Show a => Bwd a -> Doc
ppBwd = ppFwd . bwd2fwd
