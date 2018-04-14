module Shonky.Syntax where

import Control.Monad
import Control.Applicative
import Data.Char
import Text.PrettyPrint.Leijen hiding ((<$>), empty)

import Data.List
import qualified Data.Map as M

-- A program is of type [Def Exp]

data Exp
  = EV String                     -- variable
  | EI Integer                    -- integer
  | EA String                     -- atom
  | Exp :& Exp                    -- cons
  | Exp :$ [Exp]                  -- n-ary application
  | Exp :! Exp                    -- composition (;)
  | Exp :// Exp                   -- composition (o)
  | EF [[String]] [([Pat], Exp)]  -- handler
    --   [[String]]:     for each arg pos, which commands are handled
    --                   and how often (potentially multiple occurrences)?
    --   [([Pat], Exp)]: pattern matching rules
  | [Def Exp] :- Exp              -- ? (not used by Frank)
  | EX [Either Char Exp]          -- string concatenation expression
    -- (used only for characters in source Frank (Left c), but used by
    -- strcat)
  | ES [String] Exp               -- lift
    --  [String]: set of commands-to-be-lifted
  deriving (Show, Eq)
infixr 6 :&
infixl 5 :$
infixr 4 :!

data Def v
  = String := v                          -- value def
  | DF String [[String]] [([Pat], Exp)]  -- handler def
  deriving (Show, Eq)

data Pat
  = PV VPat                              -- value pattern
  | PT String                            -- variable pattern
  | PC String Integer [VPat] String      -- command pattern: cmd-id,
                                         --                  cmd-level,
                                         --                  arg-patterns,
                                         --                  contin.-var
  deriving (Show, Eq)

data VPat
  = VPV String              -- LC: ?
  | VPI Integer             -- int value
  | VPA String              -- atom value
  | VPat :&: VPat           -- cons value
  | VPX [Either Char VPat]  -- LC: ?
  | VPQ String              -- LC: ?
  deriving (Show, Eq)

pProg :: P [Def Exp]
pProg = pGap *> many (pDef <* pGap)

pGap :: P ()
pGap = () <$ many (pLike pChar isSpace)

pId :: P String
pId = do c <- pLike pChar (\c -> isAlpha c || c == '_' || c == '%')
         cs <- many (pLike pChar (\c -> isAlphaNum c || c == '\''))
         return (c : cs)

pInteger :: P Integer
pInteger = do cs <- some (pLike pChar isDigit)
              let x = concatMap (show . toInteger . digitToInt) cs
              return $ (read x :: Integer)

pP :: String -> P ()
pP s = () <$ traverse (pLike pChar . (==)) s

pExp :: P Exp
pExp = ((EV <$> pId
       <|> EI <$> pInteger
       <|> EA <$ pP "'" <*> pId
       <|> EX <$ pP "[|" <*> pText pExp
       <|> id <$ pP "[" <*> pLisp pExp (EA "") (:&)
       <|> thunk <$ pP "{" <* pGap <*> pExp <* pGap <* pP "}"
       <|> EF <$ pP "{" <* pGap <*>
          (id <$ pP "(" <*> pCSep (many (pId <* pGap)) ")"
              <* pGap <* pP ":" <* pGap
           <|> pure []) <*> pCSep pClause "" <* pGap <* pP "}"
       <|> ES <$ pP "^" <* pP "[" <*> pCSep pId "]" <* pP "("
           <*> pExp <* pP ")"
       ) >>= pApp)
     <|> (:-) <$ pP "{|" <*> pProg <* pP "|}"
                 <* pGap <*> pExp
     where thunk e = EF [] [([], e)]

pText :: P x -> P [Either Char x]
pText p = (:) <$ pP "\\" <*> (Left <$> (esc <$> pChar)) <*> pText p
    <|> (:) <$ pP "`" <*> (Right <$> p) <* pP "`" <*> pText p
    <|> [] <$ pP "|]"
    <|> (:) <$> (Left <$> pChar) <*> pText p

esc :: Char -> Char
esc 'n' = '\n'
esc 't' = '\t'
esc 'b' = '\b'
esc c   = c

pLisp :: P x -> x -> (x -> x -> x) -> P x
pLisp p n c = pGap *> (n <$ pP "]" <|> c <$> p <*> pCdr) where
  pCdr = pGap *>
    (n <$ pP "]"
    <|> id <$ pP "|" <* pGap <*> p <* pGap <* pP "]"
    <|> c <$ pP "," <* pGap <*> p <*> pCdr)

pApp :: Exp -> P Exp
pApp f = (((f :$) <$ pP "(" <*> pCSep pExp ")") >>= pApp)
       <|> (((f :!) <$ pP ";" <* pGap <*> pExp) >>= pApp)
       <|> (((f ://) <$ pP "/" <* pGap <*> pExp) >>= pApp)
       <|> pure f

-- Parses a comma-separated list, with `t` at its end
pCSep :: P x -> String -> P [x]
pCSep p t = pGap *> ((:) <$> p <*> pMore <|> [] <$ pP t) where
  pMore =  pGap *> ((:) <$ pP "," <* pGap <*> p <*> pMore <|> [] <$ pP t)

pDef :: P (Def Exp)
pDef = (:=) <$> pId <* pGap <* pP "->" <* pGap <*> pExp
  <|> (pId >>= pRules)

pClause :: P ([Pat],Exp)
pClause = (,) <$ pP "(" <*> pCSep pPat ")"
              <* pGap <* pP "->" <* pGap <*> pExp

pRules :: String -> P (Def Exp)
pRules f = DF f <$>
  (id <$ pP "(" <*> pCSep (many (pId <* pGap)) ")" <* pGap
     <* pP ":" <* pGap) <*>
  pCSep (pP f *> pClause) ""
  <|> DF f [] <$> ((:) <$> pClause <*>
       many (id <$ pGap <* pP "," <* pGap <* pP f <*> pClause))

pPat :: P Pat
pPat = PT <$ pP "{" <* pGap <*> pId <* pGap <* pP "}"
   <|> PC <$ pP "{" <* pGap <* pP "'" <*> pId <* pP "." <*> pInteger <* pP "(" <*> pCSep pVPat ")"
          <* pGap <* pP "->" <* pGap <*> pId <* pGap <* pP "}"
   <|> PV <$> pVPat

pVPat :: P VPat
pVPat = VPV <$> pId
  <|> VPI <$> pInteger
  <|> VPA <$ pP "'" <*> pId
  <|> VPX <$ pP "[|" <*> pText pVPat
  <|> VPQ <$ pP "=" <* pGap <*> pId
  <|> id <$ pP "[" <*> pLisp pVPat (VPA "") (:&:)

pLike :: P x -> (x -> Bool) -> P x
pLike p t = p >>= \ x -> if t x then return x else empty

pChar :: P Char
pChar = P $ \ s -> case s of
  (c : s) -> Just (c, s)
  [] -> Nothing

escape :: String -> String
escape = (>>= help) where
  help c | elem c "\\[|]`" = ['\\',c]
  help c = [c]

-- Parser Monad

newtype P x = P {parse :: String -> Maybe (x, String)}

instance Monad P where
  return x = P $ \ s -> Just (x, s)
  P a >>= k = P $ \ s -> do
    (x, s) <- a s
    parse (k x) s

instance Applicative P where
  pure = return
  (<*>) = ap

instance Functor P where
  fmap = ap . return

instance Alternative P where
  empty = P $ \ _ -> Nothing
  p <|> q = P $ \ s -> case parse p s of
    Nothing -> parse q s
    y -> y

-- Pretty printing routines

ppProg :: [Def Exp] -> Doc
ppProg xs = vcat (map ppDef xs)

ppDef :: Def Exp -> Doc
ppDef (id := e) = text id <+> text "->" <+> ppExp e
ppDef (DF id [] []) = error "ppDef invariant broken: empty Def Exp detected."
ppDef p@(DF id hss es) = header <$$>
                         vcat (punctuate comma cs)
  where header = text id <> parens (hcat args) <> colon
        args = punctuate comma $ (map (hsep . map text) hss)
        cs = map (\x -> text id <> (ppClause x)) es

ppText :: (a -> Doc) -> [Either Char a] -> Doc
ppText f ((Left c) : xs) = (text $ escChar c) <> (ppText f xs)
ppText f ((Right x) : xs) = text "`" <> f x <> text "`" <> (ppText f xs)
ppText f [] = text "|]"

isEscChar :: Char -> Bool
isEscChar c = any (c ==) ['\n','\t','\b']

escChar :: Char -> String
escChar c = f [('\n', "\\n"),('\t', "\\t"),('\b', "\\b")]
  where f ((c',s):xs) = if c == c' then s else f xs
        f [] = [c]

ppClause :: ([Pat], Exp) -> Doc
ppClause (ps, e) = rhs <+> text "->" <+> nest 3 lhs
  where rhs = parens (hcat $ punctuate comma (map ppPat ps))
        lhs = ppExp e

ppExp :: Exp -> Doc
ppExp (EV x) = text x
ppExp (EI n) = integer n
ppExp (EA x) = text $ "'" ++ x
ppExp (e :& e') | isListExp e = text "[" <> ppListExp e'
ppExp p@(_ :& _) = text "[" <> ppExp' p
ppExp (f :$ xs) = ppExp f <> text "(" <> (hcat $ punctuate comma (map ppExp xs)) <> text ")"
ppExp (e :! e') = ppExp e <> semi <> ppExp e'
ppExp (e :// e') = ppExp e <> text "/" <> ppExp e'
ppExp (EF xs ys) =
  let clauses = map ppClause ys in
  braces $ hcat (punctuate comma clauses)
ppExp (EX xs) = text "[|" <> ppText ppExp xs
ppExp (ES cs e) = text "^" <> brackets (hcat $ punctuate comma (map text cs)) <> parens (ppExp e)

ppExp' :: Exp -> Doc
ppExp' (e :& EA "") = ppExp e <> text "]"
ppExp' (e :& es) = ppExp e <> text "," <> ppExp' es
ppExp' e = ppExp e

isListExp :: Exp -> Bool
isListExp (e :& _) = isListExp e
isListExp _ = False

-- Special case for lists
ppListExp :: Exp -> Doc
ppListExp (e :& EA "") = ppExp e <> text "]"
ppListExp (e :& es) = ppExp e <> text "|" <> ppListExp es
ppListExp (EA "") = text "]"
ppListExp _ = text "ppListExp: invariant broken"

ppPat :: Pat -> Doc
ppPat (PV x) = ppVPat x
ppPat (PT x) = braces $ text x
ppPat (PC cmd n ps k) = braces $ text "'" <> text (cmd ++ ".") <> integer n <> parens args <+> text "->" <+> text k
  where args = vcat $ punctuate comma (map ppVPat ps)

ppVPat :: VPat -> Doc
ppVPat (VPV x) = text x
ppVPat (VPI n) = integer n
ppVPat (VPA x) = text $ "'" ++ x
ppVPat (VPX xs) = text "[|" <> ppText ppVPat xs
ppVPat (v1 :&: v2 :&: v3) = ppVPat (v1 :&: (v2 :&: v3))
ppVPat (v :&: v') | isListPat v = text "[" <> ppVPatList v'
ppVPat p@(_ :&: _) = text "[" <> ppVPat' p

ppVPatList :: VPat -> Doc
ppVPatList (v :&: VPA "") = ppVPat v <> text "]"
ppVPatList (v :&: vs) = ppVPat v <> text "|" <> ppVPatList vs
ppVPatList (VPA "") = text "]"
ppVPatList _ = error "ppVPatList: broken invariant"

ppVPat' :: VPat -> Doc
ppVPat' (v :&: VPA "") = ppVPat v <> text "]"
ppVPat' (v :&: vs) = ppVPat v <> text "," <> ppVPat' vs
ppVPat' v = ppVPat v

isListPat :: VPat -> Bool
isListPat (v :&: _) = isListPat v
isListPat _ = False
