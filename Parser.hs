{-# LANGUAGE PackageImports, ConstraintKinds #-}
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

type MonadicParsing m = (TokenParsing m, Monad m)

frankStyle :: MonadicParsing m => IdentifierStyle m
frankStyle = IdentifierStyle {
    _styleName = "Frank"
  , _styleStart = satisfy isAlpha
  , _styleLetter = satisfy (\c -> isAlpha c || c == '\'')
  , _styleReserved = HashSet.fromList ["data", "interface"]
  , _styleHighlight = Hi.Identifier
  , _styleReservedHighlight = Hi.ReservedIdentifier }

identifier :: MonadicParsing m => m String
identifier = Tok.ident frankStyle

reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve frankStyle

prog :: (Applicative m, MonadicParsing m, IndentationParsing m) => m RawProg
prog = MkRawProg <$> many tterm

tterm :: (MonadicParsing m, IndentationParsing m) => m RawTopTm
tterm = MkRawDataTm <$> parseDataT <|>
        MkRawSigTm <$> try parseMHSig <|>
        MkRawDefTm <$> parseMHCls <|>
        MkRawItfTm <$> parseItf

parseDataT :: (MonadicParsing m, IndentationParsing m) => m DataT
parseDataT = do reserved "data"
                name <- identifier
                symbol "="
                xs <- localIndentation Gt ctrlist
                return $ MkDT name xs

ctrlist :: (MonadicParsing m, IndentationParsing m) => m [Ctr]
ctrlist = sepBy parseCtr (symbol "|")

parseCtr :: MonadicParsing m => m Ctr
parseCtr = do name <- identifier
              args <- many parseVType
              return $ MkCtr name args

parseMHSig :: (MonadicParsing m, IndentationParsing m) => m MHSig
parseMHSig = do name <- identifier
                symbol ":"
                ty <- parseCType
                return (MkSig name ty)

parseMHCls :: (MonadicParsing m, IndentationParsing m) => m MHCls
parseMHCls = do name <- identifier
                ps <- many parsePattern
                symbol "="
                tm <- localIndentation Gt parseRawTm
                return $ MkMHCls name (MkRawCls ps tm)

parseItf :: (MonadicParsing m, IndentationParsing m) => m Itf
parseItf = do reserved "interface"
              name <- identifier
              ps <- many identifier
              symbol "="
              xs <- localIndentation Gt $ sepBy1 parseCmd (symbol "|")
              return (MkItf name ps xs)

parseCmd :: MonadicParsing m => m Cmd
parseCmd = do cmd <- identifier
              symbol ":"
              sig <- parseCType
              return (MkCmd cmd sig)

parseCType :: MonadicParsing m => m CType
parseCType = do (ports, peg) <- parsePortsAndPeg
                return $ MkCType ports peg

parsePortsAndPeg :: MonadicParsing m => m ([Port], Peg)
parsePortsAndPeg = try (do port <- parsePort
                           symbol "->" -- Might fail; previous parse was peg.
                           (ports, peg) <- parsePortsAndPeg
                           return (port : ports, peg)) <|>
                       (do peg <- parsePeg
                           return ([], peg))

parsePort :: MonadicParsing m => m Port
parsePort = do m <- optional $ between (symbol "<") (symbol ">")
                    (sepBy parseAdj' (symbol ","))
               let port = (case m of
                              Nothing -> MkIdAdj
                              Just es -> makeAdj es MkIdAdj)
               ty <- parseVType
               return $ MkPort port ty

parsePeg :: MonadicParsing m => m Peg
parsePeg = do m <- optional $ between (symbol "[") (symbol "]")
                   (sepBy parseAb' (symbol ","))
              let peg = (case m of
                            Nothing -> MkOpenAb
                            Just es -> makeAb es MkOpenAb)
              ty <- parseVType
              return $ MkPeg peg ty

parseAdj' :: MonadicParsing m => m Adj
parseAdj' = do x <- identifier
               ts <- many parseVType
               return (MkAdjPlus MkIdAdj x ts)

makeAdj :: [Adj] -> Adj -> Adj
makeAdj ((MkAdjPlus MkIdAdj id ts) : adjs) adj =
  makeAdj adjs (MkAdjPlus adj id ts)
makeAdj [] adj = adj
makeAdj _ _ = error "expected identity adjustment"

parseAb' :: MonadicParsing m => m Ab
parseAb' = do x <- identifier
              ts <- many parseVType
              return (MkAbPlus MkOpenAb x ts)

makeAb :: [Ab] -> Ab -> Ab
makeAb ((MkAbPlus MkOpenAb id ts) : abs) ab = makeAb abs (MkAbPlus ab id ts)
makeAb [] ab = ab
makeAb _ _ = error "expected open ability"

parseVType :: MonadicParsing m => m VType
parseVType = MkSCTy <$> try (between (symbol "{") (symbol "}") parseCType) <|>
             MkTVar <$> identifier

parseRawTm :: (MonadicParsing m, IndentationParsing m) => m RawTm
parseRawTm = MkRawSC <$> parseRawSComp <|>
             try parseComb <|>
             parseRawTm'

parseId :: (MonadicParsing m, IndentationParsing m) => m RawTm
parseId = do x <- identifier
             return $ MkRawId x

parseRawTm' :: (MonadicParsing m, IndentationParsing m) => m RawTm
parseRawTm' = parens parseRawTm <|> parseId

parseComb :: (MonadicParsing m, IndentationParsing m) => m RawTm
parseComb = do x <- identifier
               args <- choice [some parseRawTm', symbol "!" >> pure []]
               return $ MkRawComb x args

parseRawClause :: (MonadicParsing m, IndentationParsing m) => m RawClause
parseRawClause = do ps <- sepBy1 (parseVPat >>= return . MkVPat) (symbol ",")
                    symbol "->"
                    tm <- parseRawTm
                    return $ MkRawCls ps tm

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

parseRawSComp :: (MonadicParsing m, IndentationParsing m) => m RawSComp
parseRawSComp =
  absoluteIndentation $ do cs <- between (symbol "{") (symbol "}") $
                                 sepBy1 parseRawClause (symbol "|")
                           return $ MkRawSComp cs

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
expfiles = ["tests/evalState.expected"]
expectedRes = map getExpectedOutput expfiles

getExpectedOutput :: String -> IO RawProg
getExpectedOutput fname = do src <- readFile fname
                             return (read src :: RawProg)

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
    zip input $ map (uncurry assertParsedOk) (zip outputc expectedRes),
    testGroup "token parsing" $
    map (uncurry testCase) $
    zip input $ map (uncurry assertParsedOk) (zip outputt expectedRes)
  ]

