{-# LANGUAGE PackageImports, ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
-- A simple parser for the Frank language
module Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class

import Text.Trifecta
import "indentation-trifecta" Text.Trifecta.Indentation

import Data.Char
import Text.Parser.Token as Tok
import qualified Text.Parser.Token.Highlight as Hi
import qualified Data.HashSet as HashSet

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertFailure, Assertion)

import Syntax
import qualified ExpectedTestOutput as ETO

type MonadicParsing m = (TokenParsing m, IndentationParsing m, Monad m)

frankStyle :: MonadicParsing m => IdentifierStyle m
frankStyle = IdentifierStyle {
    _styleName = "Frank"
  , _styleStart = satisfy (\c -> isAlpha c || c == '_')
  , _styleLetter = satisfy (\c -> isAlpha c || c == '_' || c == '\'')
  , _styleReserved = HashSet.fromList ["data", "interface", "String", "Int"]
  , _styleHighlight = Hi.Identifier
  , _styleReservedHighlight = Hi.ReservedIdentifier }

identifier :: MonadicParsing m => m String
identifier = Tok.ident frankStyle

reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve frankStyle

prog :: (Applicative m, MonadicParsing m) => m (Prog Raw)
prog = MkProg <$> many tterm

tterm :: MonadicParsing m => m (TopTm Raw)
tterm = MkDataTm <$> parseDataT <|>
        MkSigTm <$> try parseMHSig <|>
        MkClsTm <$> parseMHCls <|>
        MkItfTm <$> parseItf

parseDataT :: MonadicParsing m => m (DataT Raw)
parseDataT = do reserved "data"
                name <- identifier
                ps <- many identifier
                symbol "="
                xs <- localIndentation Gt ctrlist
                return $ MkDT name ps xs

ctrlist :: MonadicParsing m => m [Ctr Raw]
ctrlist = sepBy parseCtr (symbol "|")

parseCtr :: MonadicParsing m => m (Ctr Raw)
parseCtr = do name <- identifier
              args <- many parseVType
              return $ MkCtr name args

parseMHSig :: MonadicParsing m => m MHSig
parseMHSig = do name <- identifier
                symbol ":"
                ty <- parseCType
                return (MkSig name ty)

parseMHCls :: MonadicParsing m => m MHCls
parseMHCls = do name <- identifier
                ps <- many parsePattern
                symbol "="
                seq <- localIndentation Gt parseRawTmSeq
                return $ MkMHCls name (MkCls ps seq)

parseItf :: MonadicParsing m => m (Itf Raw)
parseItf = do reserved "interface"
              name <- identifier
              ps <- many identifier
              symbol "="
              xs <- localIndentation Gt $ sepBy1 parseCmd (symbol "|")
              return (MkItf name ps xs)

parseCmd :: MonadicParsing m => m (Cmd Raw)
parseCmd = do cmd <- identifier
              symbol ":"
              sig <- parseCType
              return (MkCmd cmd sig)

parseCType :: MonadicParsing m => m (CType Raw)
parseCType = do (ports, peg) <- parsePortsAndPeg
                return $ MkCType ports peg

parsePortsAndPeg :: MonadicParsing m => m ([Port Raw], Peg Raw)
parsePortsAndPeg = try (do port <- parsePort
                           symbol "->" -- Might fail; previous parse was peg.
                           (ports, peg) <- parsePortsAndPeg
                           return (port : ports, peg)) <|>
                       (do peg <- parsePeg
                           return ([], peg))

parsePort :: MonadicParsing m => m (Port Raw)
parsePort = do adj <- parseAdj
               ty <- parseVType
               return $ MkPort adj ty

parsePeg :: MonadicParsing m => m (Peg Raw)
parsePeg = do ab <- parseAb
              ty <- parseVType
              return $ MkPeg ab ty

parseAdj :: MonadicParsing m => m (Adj Raw)
parseAdj = do adj <- optional $ angles (sepBy parseAdj' (symbol ","))
              case adj of
                Nothing -> return MkIdAdj
                Just es -> return $ makeAdj es MkIdAdj

parseAdj' :: MonadicParsing m => m (Adj Raw)
parseAdj' = do x <- identifier
               ts <- many parseVType
               return (MkAdjPlus MkIdAdj x ts)

makeAdj :: [Adj Raw] -> Adj Raw -> Adj Raw
makeAdj ((MkAdjPlus MkIdAdj id ts) : adjs) adj =
  makeAdj adjs (MkAdjPlus adj id ts)
makeAdj [] adj = adj
makeAdj _ _ = error "expected identity adjustment"

parseDTAb :: MonadicParsing m => m (Ab Raw)
parseDTAb = do ab <- optional $ brackets (sepBy parseAb' (symbol ","))
               case ab of
                 Nothing -> return $ MkEmpAb -- pure data types
                 Just es -> return $ makeAb es MkOpenAb

parseAb :: MonadicParsing m => m (Ab Raw)
parseAb = do ab <- optional $ brackets (sepBy parseAb' (symbol ","))
             case ab of
               Nothing -> return MkOpenAb
               Just es -> return $ makeAb es MkOpenAb

parseAb' :: MonadicParsing m => m (Ab Raw)
parseAb' = do x <- identifier
              ts <- many parseVType
              return (MkAbPlus MkOpenAb x ts)

makeAb :: [Ab Raw] -> Ab Raw -> Ab Raw
makeAb ((MkAbPlus MkOpenAb id ts) : abs) ab = makeAb abs (MkAbPlus ab id ts)
makeAb [] ab = ab
makeAb _ _ = error "expected open ability"

parseVType :: MonadicParsing m => m (VType Raw)
parseVType = try parseDTType <|>
             parseVType'

parseVType' :: MonadicParsing m => m (VType Raw)
parseVType' = parens parseVType <|>
              MkSCTy <$> try (braces parseCType) <|>
              MkStringTy <$ reserved "String" <|>
              MkIntTy <$ reserved "Int" <|>
              MkTVar <$> identifier

-- Parse a potential datatype. Note it may actually be a type variable.
parseDTType :: MonadicParsing m => m (VType Raw)
parseDTType = do x <- identifier
                 ab <- parseDTAb
                 ps <- localIndentation Gt $ many parseVType'
                 return $ MkDTTy x ab ps

parseRawTmSeq :: MonadicParsing m => m (Tm Raw)
parseRawTmSeq = try (do tm1 <- parseRawTm
                        symbol ";"
                        tm2 <- parseRawTm
                        return $ MkTmSeq tm1 tm2) <|>
                parseRawTm

parseRawTm :: MonadicParsing m => m (Tm Raw)
parseRawTm = MkSC <$> parseRawSComp <|>
             try parseComb <|>
             parseRawTm'

parseId :: MonadicParsing m => m (Tm Raw)
parseId = do x <- identifier
             return $ MkRawId x

parseNullaryComb :: MonadicParsing m => m (Tm Raw)
parseNullaryComb = do x <- identifier
                      symbol "!"
                      return $ MkRawComb x []

parseRawTm' :: MonadicParsing m => m (Tm Raw)
parseRawTm' = parens parseRawTmSeq <|>
              try parseNullaryComb <|>
              parseId <|>
              MkStr <$> stringLiteral <|>
              MkInt <$> integer

parseComb :: MonadicParsing m => m (Tm Raw)
parseComb = do x <- identifier
               args <- choice [some parseRawTm', symbol "!" >> pure []]
               return $ MkRawComb x args

parseRawClause :: MonadicParsing m => m (Clause Raw)
parseRawClause = do ps <- sepBy1 (parseVPat >>= return . MkVPat) (symbol ",")
                    symbol "->"
                    seq <- parseRawTmSeq
                    return $ MkCls ps seq

parsePattern :: MonadicParsing m => m Pattern
parsePattern = try parseCPat <|> MkVPat <$> parseVPat

parseCPat :: MonadicParsing m => m Pattern
parseCPat = between (symbol "<") (symbol ">") $
            try parseCmdPat <|> parseThunkPat

parseThunkPat :: MonadicParsing m => m Pattern
parseThunkPat = do x <- identifier
                   return (MkThkPat x)

parseCmdPat :: MonadicParsing m => m Pattern
parseCmdPat = do cmd <- identifier
                 ps <- many parseVPat
                 symbol "->"
                 g <- identifier
                 return (MkCmdPat cmd ps g)

parseVPat :: MonadicParsing m => m ValuePat
parseVPat = parseDataTPat <|> (do x <- identifier
                                  return $ MkVarPat x)

parseDataTPat :: MonadicParsing m => m ValuePat
parseDataTPat = between (symbol ")") (symbol ")") $ do k <- identifier
                                                       ps <- many parseVPat
                                                       return $ MkDataPat k ps

parseRawSComp :: MonadicParsing m => m (SComp Raw)
parseRawSComp =
  absoluteIndentation $ do cs <- between (symbol "{") (symbol "}") $
                                 sepBy1 parseRawClause (symbol "|")
                           return $ MkSComp cs

evalCharIndentationParserT :: Monad m => IndentationParserT Char m a ->
                              IndentationState -> m a
evalCharIndentationParserT = evalIndentationParserT

evalTokenIndentationParserT :: Monad m => IndentationParserT Token m a ->
                               IndentationState -> m a
evalTokenIndentationParserT = evalIndentationParserT

runParse ev input
 = let indA = ev prog $ mkIndentationState 0 infIndentation True Ge
   in case parseString indA mempty input of
    Failure err -> Left (show err)
    Success t -> Right t

runParseFromFileEx ev fname =
  let indA = ev prog $ mkIndentationState 0 infIndentation True Ge in
  do res <- parseFromFileEx indA fname
     case res of
       Failure err -> return $ Left (show err)
       Success t -> return $ Right t

runCharParseFromFile = runParseFromFileEx evalCharIndentationParserT
runTokenParseFromFile = runParseFromFileEx evalTokenIndentationParserT

runCharParse = runParse evalCharIndentationParserT
runTokenParse = runParse evalTokenIndentationParserT

input = ["tests/evalState.fk"]

outputc = map runCharParseFromFile input
outputt = map runTokenParseFromFile input

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

allTests :: TestTree
allTests =
  testGroup "Frank (trifecta)"
  [
    testGroup "char parsing" $
    map (uncurry testCase) $
    zip input $ map (uncurry assertParsedOk) (zip outputc ETO.expected),
    testGroup "token parsing" $
    map (uncurry testCase) $
    zip input $ map (uncurry assertParsedOk) (zip outputt ETO.expected)
  ]
