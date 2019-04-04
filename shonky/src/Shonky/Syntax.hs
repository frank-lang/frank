module Shonky.Syntax where

import Control.Monad
import Control.Applicative
import Data.Char
import Text.PrettyPrint hiding ((<$>), empty)

import Data.List
import qualified Data.Map as M

import Shonky.Renaming

-- A program is of type [Def Exp]

data Exp
  = EV String                               -- variable
  | EI Int                                  -- int
  | EA String                               -- atom
  | Exp :& Exp                              -- cons
  | Exp :$ [Exp]                            -- n-ary application
  | Exp :! Exp                              -- composition (;)
  | Exp :// Exp                             -- composition (o)
  | EF [([Adap], [String])] [([Pat], Exp)]  -- handler                      -- [([Adap], [String])]:     for each arg pos, which adaptors are applied and which commands are handled and how often (potentially multiple occurrences)?
                                                                            -- [([Pat], Exp)]: pattern matching rules
  | [Def Exp] :- Exp                        -- ? (not used by Frank)
  | EX [Either Char Exp]                    -- string concat expression
    -- (used only for characters in source Frank (Left c), but used by
    -- strcat)
  | ER Adap Exp                             -- adapted exp
  deriving (Show, Eq)
infixr 6 :&
infixl 5 :$
infixr 4 :!

data Def v
  = String := v                                     -- value def
  | DF String [([Adap], [String])] [([Pat], Exp)]   -- handler def: (like EF, but with name)
                                                    -- - name
                                                    -- - redirection, executed
                                                    --     before assigning
                                                    --     commands to arg pos
                                                    -- - commands at args
                                                    -- - patterns + bodies
  deriving (Show, Eq)

{--
 -- Datatype of Patterns:
 --   * PV is for value patterns,
 --   * PT is for variable patterns,
 --   * PC is for command patterns.
 --}
data Pat
  = PV VPat
  | PT String
  | PC String Int [VPat] String
  deriving (Show, Eq)

data VPat
  = VPV String              -- LC: ?
  | VPI Int                 -- int value
  | VPA String              -- atom value
  | VPat :&: VPat           -- cons value
  | VPX [Either Char VPat]  -- LC: ?
  | VPQ String              -- LC: ?
  deriving (Show, Eq)

-- [String]   commands to be adapted
-- Renaming
type Adap = ([String], Renaming)

pProg :: P [Def Exp]
pProg = pGap *> many (pDef <* pGap)

pGap :: P ()
pGap = () <$ many (pLike pChar isSpace)

pId :: P String
pId = do c <- pLike pChar (\c -> isAlpha c || c == '_' || c == '%')
         cs <- many (pLike pChar (\c -> isAlphaNum c || c == '\''))
         return (c : cs)

pInt :: P Int
pInt = do cs <- some (pLike pChar isDigit)
          let x = concatMap (show . digitToInt) cs
          return $ (read x :: Int)

pP :: String -> P ()
pP s = () <$ traverse (pLike pChar . (==)) s

pExp :: P Exp
pExp = ((((\x -> ER (x, renRem 0)) <$ pGap <* pP "neg" <* pGap <* pP "<" <* pGap <*>
          pCSep (pId <* pGap) ">" <*
          pGap <* pP "(" <* pGap <*>
          pExp <*
          pGap <* pP ")" <* pGap)
       <|> EV <$> pId
       <|> EI <$> pInt
       <|> EA <$ pP "'" <*> pId
       <|> EX <$ pP "[|" <*> pText pExp
       <|> id <$ pP "[" <*> pLisp pExp (EA "") (:&)
       <|> thunk <$ pP "{" <* pGap <*> pExp <* pGap <* pP "}"
       <|> EF <$ pP "{" <* pGap <*>
          (id <$ pP "(" <*> (map (\x -> ([], x)) <$> pCSep (many (pId <* pGap)) ")")
              <* pGap <* pP ":" <* pGap
           <|> pure [])
          <*> pCSep pClause "" <* pGap <* pP "}"
       ) >>= pApp)
       <|> (:-) <$ pP "{|" <*> pProg <* pP "|}" <* pGap <*> pExp
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
  (id <$ pP "(" <*> (map (\x -> ([], x)) <$> pCSep (many (pId <* pGap)) ")") <* pGap
     <* pP ":" <* pGap) <*>
  pCSep (pP f *> pClause) ""
  <|> DF f [] <$> ((:) <$> pClause <*>
       many (id <$ pGap <* pP "," <* pGap <* pP f <*> pClause))
-- TODO: LC: Parse adjustments/renamings in ports

pPat :: P Pat
pPat = PT <$ pP "{" <* pGap <*> pId <* pGap <* pP "}"
   <|> PC <$ pP "{" <* pGap <* pP "'" <*> pId <* pP "." <*> pInt <* pP "(" <*> pCSep pVPat ")"
          <* pGap <* pP "->" <* pGap <*> pId <* pGap <* pP "}"
   <|> PV <$> pVPat

pVPat :: P VPat
pVPat = VPV <$> pId
  <|> VPI <$> pInt
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
