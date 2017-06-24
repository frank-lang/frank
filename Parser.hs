{-# LANGUAGE PackageImports, ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
-- A simple parser for the Frank language
module Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class

import Text.Trifecta
import "indentation-trifecta" Text.Trifecta.Indentation

import Data.Char
import qualified Data.Map.Strict as M

import Text.Parser.Token as Tok
import Text.Parser.Token.Style
import qualified Text.Parser.Token.Highlight as Hi
import qualified Data.HashSet as HashSet

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertFailure, Assertion)

import Syntax

newtype FrankParser t m a =
  FrankParser { runFrankParser :: IndentationParserT t m a }
  deriving (Functor, Alternative, Applicative, Monad, Parsing
           , IndentationParsing)

deriving instance (DeltaParsing m) => (CharParsing (FrankParser Char m))
deriving instance (DeltaParsing m) => (CharParsing (FrankParser Token m))
deriving instance (DeltaParsing m) => (TokenParsing (FrankParser Char m))

instance DeltaParsing m => TokenParsing (FrankParser Token m) where
  someSpace = FrankParser $ buildSomeSpaceParser someSpace haskellCommentStyle
  nesting = FrankParser . nesting . runFrankParser
  semi = FrankParser $ runFrankParser semi
  highlight h = FrankParser . highlight h . runFrankParser
  token p = (FrankParser $ token (runFrankParser p)) <* whiteSpace

type MonadicParsing m = (TokenParsing m, IndentationParsing m, Monad m)

frankStyle :: MonadicParsing m => IdentifierStyle m
frankStyle = IdentifierStyle {
    _styleName = "Frank"
  , _styleStart = satisfy (\c -> isAlpha c || c == '_')
  , _styleLetter = satisfy (\c -> isAlphaNum c || c == '_' || c == '\'')
  , _styleReserved = HashSet.fromList [ "data", "interface"
                                      , "let", "in"
                                      , "String", "Int", "Char"]
  , _styleHighlight = Hi.Identifier
  , _styleReservedHighlight = Hi.ReservedIdentifier }

identifier :: MonadicParsing m => m String
identifier = Tok.ident frankStyle

reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve frankStyle

-- the eof disallows gibberish at the end of the file!
prog :: (Applicative m, MonadicParsing m) => m (Prog Raw)
prog = MkProg <$ whiteSpace <*> do tts <- many tterm; eof; return tts

tterm :: MonadicParsing m => m (TopTm Raw)
tterm = MkDataTm <$> parseDataT <|>
        MkSigTm <$> try parseMHSig <|>
        MkClsTm <$> parseMHCls <|>
        MkItfTm <$> try parseItf <|>
        MkItfAliasTm <$> parseItfAlias

parseTyVar :: MonadicParsing m => m (Id, Kind)
parseTyVar = (\x -> (x, ET)) <$> brackets parseEVar <|>
             (\x -> (x, VT)) <$> identifier

parseDataT :: MonadicParsing m => m (DataT Raw)
parseDataT = do reserved "data"
                name <- identifier
                ps <- many parseTyVar
                symbol "="
                cs <- localIndentation Gt ctrlist
                return $ MkDT name ps cs

parseEVar :: MonadicParsing m => m Id
parseEVar = do mx <- optional identifier
               case mx of
                 Nothing -> return "£"
                 Just x -> return x

ctrlist :: MonadicParsing m => m [Ctr Raw]
ctrlist = sepBy parseCtr (symbol "|")

parseCtr :: MonadicParsing m => m (Ctr Raw)
parseCtr = do name <- identifier
              args <- many parseVType'
              return $ MkCtr name args

parseMHSig :: MonadicParsing m => m MHSig
parseMHSig = do name <- identifier
                symbol ":"
                ty <- parseSigType
                return (MkSig name ty)

-- As the outer braces are optional in top-level signatures we require
-- that plain pegs must have explicit ability brackets.
--
-- The following collections of signatures are equivalent:
--
--   f : {A -> B -> C}  and  f : A -> B -> C
--   x : {Int}  and  x : {[]Int}  and x : []Int
--
-- A signature of the form
--
--   x : Int
--
-- is not currently valid. Once we add support for top level values it
-- will become valid, but will not mean the same thing as:
--
--   x : []Int
parseSigType :: MonadicParsing m => m (CType Raw)
parseSigType = (do symbol "{"
                   ct <- parseCType
                   symbol "}"
                   rest <- optional (symbol "->" *> parseCType)
                   return $
                     case rest of
                       Nothing -> ct
                       Just (MkCType ports peg) ->
                         MkCType ((MkPort idAdj (MkSCTy ct)) : ports) peg) <|>
               (do ports <- some (try (parsePort <* symbol "->"))
                   peg <- parsePeg
                   return $ MkCType ports peg) <|>
               (do peg <- parsePegExplicit
                   return $ MkCType [] peg)

parseMHCls :: MonadicParsing m => m MHCls
parseMHCls = do name <- identifier
                ps <- choice [some parsePattern, symbol "!" >> return []]
                symbol "="
                seq <- localIndentation Gt parseRawTmSeq
                return $ MkMHCls name (MkCls ps seq)

parseItf :: MonadicParsing m => m (Itf Raw)
parseItf = do reserved "interface"
              name <- identifier
              ps <- many parseTyVar
              symbol "="
              xs <- localIndentation Gt $ sepBy1 parseCmd (symbol "|")
              return (MkItf name ps xs)

parseCmd :: MonadicParsing m => m (Cmd Raw)
parseCmd = do cmd <- identifier
              ps <- many parseTyVar  -- polymorphic commands
              symbol ":"
              (xs,y) <- parseCmdType
              return (MkCmd cmd ps xs y)

-- type vars, input types, output type
parseCmdType :: MonadicParsing m => m ([VType Raw], VType Raw)
parseCmdType = do vs <- sepBy1 parseVType (symbol "->")
                  if length vs == 1 then return ([],head vs)
                  else return (init vs, last vs)

parseItfAlias :: MonadicParsing m => m (ItfAlias Raw)
parseItfAlias = do reserved "interface"
                   name <- identifier
                   ps <- many parseTyVar
                   symbol "="
                   symbol "["
                   xs <- parseItfInstances
                   symbol "]"
                   return $ MkItfAlias name ps (M.fromList xs)

parseCType :: MonadicParsing m => m (CType Raw)
parseCType = do ports <- many (try (parsePort <* symbol "->"))
                peg <- parsePeg
                return $ MkCType ports peg

parsePort :: MonadicParsing m => m (Port Raw)
parsePort = do adj <- parseAdj
               ty <- parseVType
               return $ MkPort adj ty

parsePeg :: MonadicParsing m => m (Peg Raw)
parsePeg = do ab <- parseAb
              ty <- parseVType
              return $ MkPeg ab ty

parsePegExplicit :: MonadicParsing m => m (Peg Raw)
parsePegExplicit = do ab <- brackets parseAbBody
                      ty <- parseVType
                      return $ MkPeg ab ty

parseAdj :: MonadicParsing m => m (Adj Raw)
parseAdj = do mxs <- optional $ angles (sepBy parseAdj' (symbol ","))
              case mxs of
                Nothing -> return $ MkAdj M.empty
                Just xs -> return $ MkAdj (M.fromList xs)

parseAdj' :: MonadicParsing m => m (Id, [TyArg Raw])
parseAdj' = do x <- identifier
               ts <- many parseTyArg
               return (x, ts)

parseDTAb :: MonadicParsing m => m (Ab Raw)
parseDTAb = brackets parseAbBody

parseItfInstances :: MonadicParsing m => m [(Id, [TyArg Raw])]
parseItfInstances = sepBy parseItfInstance (symbol ",")

-- 0 | 0|Interfaces | E|Interfaces | Interfaces
parseAbBody :: MonadicParsing m => m (Ab Raw)
parseAbBody = -- closed ability: [0] or [0 | i_1, ... i_n]
              (do symbol "0"
                  xs <- option [] (symbol "|" *> parseItfInstances)
                  return $ MkAb MkEmpAb (M.fromList xs)) <|>
              -- open ability:   [i_1, ..., i_n] (implicitly e := £) or [e | i_1, ..., i_n]
              (do e <- option (MkAbVar "£") (try $ MkAbVar <$> identifier <* symbol "|")
                  xs <- parseItfInstances
                  return $ MkAb e (M.fromList xs))

parseAb :: MonadicParsing m => m (Ab Raw)
parseAb = do mxs <- optional $ brackets parseAbBody
             case mxs of
               Nothing -> return $ MkAb (MkAbVar "£") M.empty
               Just ab -> return ab

parseItfInstance :: MonadicParsing m => m (Id, [TyArg Raw])
parseItfInstance = do x <- identifier
                      ts <- many parseTyArg
                      return (x, ts)

-- This parser gives higher precedence to MkDTTy when coming across "X"
-- E.g., the type "X" becomes   MkDTTy "X" []   (instead of MkTVar "X")
parseVType :: MonadicParsing m => m (VType Raw)
parseVType = try parseDTType <|> -- could possibly also be a MKTvar (determined
                                 -- during refinement)
             parseVType'

-- This parser gives higher precedence to MkTVar when coming across "X"
-- E.g., the type "X" becomes   MkTVar "X"   (instead of MkDTTy "X" [])
-- By writing "(X)" one can escape back to parseVType
parseVType' :: MonadicParsing m => m (VType Raw)
parseVType' = parens parseVType <|>
              MkSCTy <$> try (braces parseCType) <|>
              MkStringTy <$ reserved "String" <|>
              MkIntTy <$ reserved "Int" <|>
              MkCharTy <$ reserved "Char" <|>
              MkTVar <$> identifier  -- could possibly also be a MkDTTy
                                     -- (determined during refinement)

parseTyArg :: MonadicParsing m => m (TyArg Raw)
parseTyArg = VArg <$> parseVType' <|>
             EArg <$> parseDTAb

-- Parse a potential datatype. Note it may actually be a type variable.
parseDTType :: MonadicParsing m => m (VType Raw)
parseDTType = do x <- identifier
                 args <- localIndentation Gt $ many parseTyArg
                 return $ MkDTTy x args

parseRawTmSeq :: MonadicParsing m => m (Tm Raw)
parseRawTmSeq = do tm1 <- parseRawTm
                   m <- optional $ symbol ";"
                   case m of
                     Just _ -> do tm2 <- parseRawTmSeq
                                  return $ MkTmSeq tm1 tm2
                     Nothing -> return tm1

-- parse term of 1st syntactic category
parseRawTm :: MonadicParsing m => m (Tm Raw)
parseRawTm = parseLet <|>
             try parseRawOpTm <|>
             parseRawTm'

-- parse term of 2nd syntactic category
-- parse binary operation or term comb t_1 ... t_n
parseRawOpTm :: MonadicParsing m => m (Tm Raw)
parseRawOpTm = do uminus <- optional $ symbol "-"
                  t1 <- parseRawOperandTm
                  let t1' = case uminus of
                        Just _ -> MkUse $ MkRawComb (MkRawId "-") [MkInt 0,t1]
                        Nothing -> t1
                  (do op' <- choice $ map symbol ["+","-","*","/","::"]
                      let op = if op' == "::" then "cons" else op'
                      t2 <- parseRawOperandTm
                      return $ MkUse $ MkRawComb (MkRawId op) [t1',t2])
                    <|> return t1'

parseRawOperandTm :: MonadicParsing m => m (Tm Raw)
parseRawOperandTm = MkUse <$> try parseComb <|>
                    parens parseRawOpTm <|>
                    MkUse <$> parseId <|>
                    MkInt <$> natural

parseId :: MonadicParsing m => m (Use Raw)
parseId = do x <- identifier
             return $ MkRawId x

parseNullaryComb :: MonadicParsing m => m (Use Raw)
parseNullaryComb = do x <- choice [parseId, parens parseComb]
                      symbol "!"
                      return $ MkRawComb x []

parseLet :: MonadicParsing m => m (Tm Raw)
parseLet = do reserved "let"
              x <- identifier
              symbol "="
              tm1 <- parseRawTm
              reserved "in"
              tm2 <- parseRawTmSeq
              return $ MkLet x tm1 tm2

-- parse any term except let-expression or binary operation
parseRawTm' :: MonadicParsing m => m (Tm Raw)
parseRawTm' = MkUse <$> try parseNullaryComb <|>  -- x!
              parens parseRawTmSeq <|>            -- t_1 ; ... ; t_n
              MkUse <$> parseId <|>               -- x
              MkSC <$> parseRawSComp <|>          -- { p_1 -> t_1 | ...
              MkStr <$> stringLiteral <|>         -- "string"
              MkInt <$> natural <|>               -- 42
              MkChar <$> charLiteral <|>          -- 'c'
              MkList <$> listTm                   -- [t_1, ..., t_n]

listTm :: MonadicParsing m => m [Tm Raw]          -- [t_1, ..., t_n]
listTm = brackets (sepBy parseRawTm (symbol ","))

parseComb :: MonadicParsing m => m (Use Raw)
parseComb = do x <- choice [parseId, parens parseComb]
               args <- choice [some parseRawTm', symbol "!" >> pure []]
               return $ MkRawComb x args

parseRawClause :: MonadicParsing m => m (Clause Raw)
parseRawClause = do ps <- choice [try parsePatterns, pure []]
                    seq <- parseRawTmSeq
                    return $ MkCls ps seq
  where parsePatterns =
          do ps <- choice [some parsePattern, symbol "!" >> return []]
             symbol "->"
             return $ ps

parsePattern :: MonadicParsing m => m (Pattern Raw)
parsePattern = try parseCPat <|> MkVPat <$> parseVPat

parseCPat :: MonadicParsing m => m (Pattern Raw)
parseCPat = between (symbol "<") (symbol ">") $
            try parseCmdPat <|> parseThunkPat

parseThunkPat :: MonadicParsing m => m (Pattern Raw)
parseThunkPat = do x <- identifier
                   return (MkThkPat x)

parseCmdPat :: MonadicParsing m => m (Pattern Raw)
parseCmdPat = do cmd <- identifier
                 ps <- many parseVPat
                 symbol "->"
                 g <- identifier
                 return (MkCmdPat cmd ps g)

parseVPat :: MonadicParsing m => m (ValuePat Raw)
parseVPat = parseDataTPat <|>
            (do x <- identifier
                return $ MkVarPat x) <|>
            MkIntPat <$> try integer <|> -- try block for unary minus
            MkCharPat <$> charLiteral <|>
            MkStrPat <$> stringLiteral <|>
            MkListPat <$> brackets (sepBy parseVPat (symbol ","))

parseDataTPat :: MonadicParsing m => m (ValuePat Raw)
parseDataTPat = parens $ (try (do p <- parseVPat
                                  symbol "::"
                                  q <- parseVPat
                                  return $ MkConsPat p q)) <|>
                         (do k <- identifier
                             ps <- many parseVPat
                             return $ MkDataPat k ps)

parseRawSComp :: MonadicParsing m => m (SComp Raw)
parseRawSComp = localIndentation Gt $ absoluteIndentation $
                do cs <- braces $ sepBy parseRawClause (symbol "|")
                   return $ MkSComp cs

evalCharIndentationParserT :: Monad m => FrankParser Char m a ->
                              IndentationState -> m a
evalCharIndentationParserT = evalIndentationParserT . runFrankParser

evalTokenIndentationParserT :: Monad m => FrankParser Token m a ->
                               IndentationState -> m a
evalTokenIndentationParserT = evalIndentationParserT . runFrankParser

runParse ev p input
 = let indA = ev p $ mkIndentationState 0 infIndentation True Ge
   in case parseString indA mempty input of
    Failure err -> Left (show err)
    Success t -> Right t

runProgParse ev input = runParse ev prog input

runParseFromFileEx ev p fname =
  let indA = ev p $ mkIndentationState 0 infIndentation True Ge in
  do res <- parseFromFileEx indA fname
     case res of
       Failure err -> return $ Left (show err)
       Success t -> return $ Right t

runProgParseFromFileEx ev fname = runParseFromFileEx ev prog fname

--runCharParseFromFile = runParseFromFileEx evalCharIndentationParserT
runTokenParseFromFile :: (MonadIO m, Applicative m, MonadicParsing m) =>
                         String -> m (Either String (Prog Raw))
runTokenParseFromFile = runProgParseFromFileEx evalTokenIndentationParserT

--runCharParse = runParse evalCharIndentationParserT
runTokenParse p = runParse evalTokenIndentationParserT p
runTokenProgParse = runProgParse evalTokenIndentationParserT

input = [ "tests/evalState.fk"
        , "tests/listMap.fk"
        , "tests/suspended_computations.fk"
        , "tests/fib.fk"
        , "tests/paper.fk"]

--outputc = map runCharParseFromFile input
--outputt = map runTokenParseFromFile input

assertParsedOk :: (Show err, Show a, Eq a) => IO (Either err a) -> IO a
                  -> Assertion
assertParsedOk actual expected =
  do x <- actual
     case x of
       Right ok -> do y <- expected
                      assertEqual "parsing succeeded, but " y ok
       Left err -> do y <- expected
                      assertFailure ("parse failed with " ++ show err
                                     ++ ", expected " ++ show y)
