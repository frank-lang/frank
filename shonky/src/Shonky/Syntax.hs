module Shonky.Syntax where

import Control.Monad
import Control.Applicative
import Data.Char

import Data.List
import qualified Data.Map as M

data Exp
  = EV String                     -- variable
  | EI Integer                    -- integer
  | EA String                     -- atom
  | Exp :& Exp                    -- cons
  | Exp :$ [Exp]                  -- application
  | Exp :! Exp                    -- composition (;)
  | Exp :// Exp                   -- composition (o)
  | EF [[String]] [([Pat], Exp)]  -- operator
  | [Def Exp] :- Exp              -- ? (not used by Frank)
  | EX [Either Char Exp]          -- string concatenation expression
                                  -- (only used for characters in source Frank (Left c), but used by strcat)
  deriving (Show, Eq)
infixr 6 :&
infixl 5 :$
infixr 4 :!

data Def v
  = String := v
  | DF String [[String]] [([Pat], Exp)]
  deriving (Show, Eq)

data Pat
  = PV VPat
  | PT String
  | PC String [VPat] String
  deriving (Show, Eq)

data VPat
  = VPV String
  | VPI Integer
  | VPA String
  | VPat :&: VPat
  | VPX [Either Char VPat]
  | VPQ String
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
   <|> PC <$ pP "{" <* pGap <* pP "'" <*> pId <* pP "(" <*> pCSep pVPat ")"
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

ppProg :: [Def Exp] -> String
ppProg xs = unlines $ map ppDef xs

ppDef :: Def Exp -> String
ppDef (id := e) = id ++ " -> " ++ ppExp e
ppDef (DF id [] [])  = error "ppDef invariant broken: empty Def Exp detected."
ppDef (DF id [] ys) = ppCSep (\x -> id ++ (ppClause x)) ys
ppDef p@(DF id xs ys) = unlines hdr
  where hdr = [header, cs]
        header = id ++ "(" ++ args ++ "):"
        args = intercalate "," (map (intercalate " ") xs)
        cs = unlines $ f $ map (\x -> id ++ (ppClause x)) ys
        f (xs:[]) = [xs] -- don't add separator in last case
        f (xs:xss) = (xs ++ ",") : f xss

ppCSep :: (a -> String) -> [a] -> String
ppCSep f xs = intercalate "," $ map f xs

ppText :: (a -> String) -> [Either Char a] -> String
ppText f ((Left c) : xs) = escChar c ++ (ppText f xs)
ppText f ((Right x) : xs) = "`" ++ (f x) ++ "`" ++ (ppText f xs)
ppText f [] = "|]"

isEscChar :: Char -> Bool
isEscChar c = any (c ==) ['\n','\t','\b']

escChar :: Char -> String
escChar c = f [('\n', "\\n"),('\t', "\\t"),('\b', "\\b")]
  where f ((c',s):xs) = if c == c' then s else f xs
        f [] = [c]

ppClause :: ([Pat], Exp) -> String
ppClause (ps, e) = rhs ++ " -> " ++ lhs
  where rhs = "(" ++ (ppCSep ppPat ps) ++ ")"
        lhs = ppExp e

ppExp :: Exp -> String
ppExp (EV x) = x
ppExp (EI n) = show n
ppExp (EA x) = "'" ++ x
ppExp (EX xs) = "[|" ++ ppText ppExp xs
ppExp (e :& e') | isListExp e = "[" ++ ppListExp e'
ppExp p@(_ :& _) = "[" ++ ppExp' p
ppExp (f :$ xs) = ppExp f ++ "(" ++ ppCSep ppExp xs ++ ")"
ppExp (e :! e') = ppExp e ++ ";" ++ ppExp e'
ppExp (e :// e') = ppExp e ++ "/" ++ ppExp e'
ppExp (EF xs ys) =
  let clauses = ppCSep (\x -> ppClause x) ys in
  "{" ++ clauses ++ "}"

ppExp' :: Exp -> String
ppExp' (e :& EA "") = ppExp e ++ "]"
ppExp' (e :& es) = ppExp e ++ "," ++ ppExp' es
ppExp' e = ppExp e

isListExp :: Exp -> Bool
isListExp (e :& _) = isListExp e
isListExp _ = False

-- Special case for lists
ppListExp :: Exp -> String
ppListExp (e :& EA "") = ppExp e ++ "]"
ppListExp (e :& es) = ppExp e ++ "|" ++ ppListExp es
ppListExp (EA "") = "]"
ppListExp _ = "ppListExp: invariant broken"

ppPat :: Pat -> String
ppPat (PV x) = ppVPat x
ppPat (PT x) = "{" ++ x ++ "}"
ppPat (PC cmd ps k) = "{'" ++ cmd ++ "(" ++ args ++ ") -> " ++ k ++ "}"
  where args = ppCSep ppVPat ps

ppVPat :: VPat -> String
ppVPat (VPV x) = x
ppVPat (VPI n) = show n
ppVPat (VPA x) = "'" ++ x
ppVPat (VPX xs) = "[|" ++ ppText ppVPat xs
ppVPat (v1 :&: v2 :&: v3) = ppVPat (v1 :&: (v2 :&: v3))
ppVPat (v :&: v') | isListPat v = "[" ++ ppVPatList v'
ppVPat p@(_ :&: _) = "[" ++ ppVPat' p

ppVPatList :: VPat -> String
ppVPatList (v :&: VPA "") = ppVPat v ++ "]"
ppVPatList (v :&: vs) = ppVPat v ++ "|" ++ ppVPatList vs
ppVPatList (VPA "") = "]"
ppVPatList _ = error "ppVPatList: broken invariant"

ppVPat' :: VPat -> String
ppVPat' (v :&: VPA "") = ppVPat v ++ "]"
ppVPat' (v :&: vs) = ppVPat v ++ "," ++ ppVPat' vs
ppVPat' v = ppVPat v

isListPat :: VPat -> Bool
isListPat (v :&: _) = isListPat v
isListPat _ = False
