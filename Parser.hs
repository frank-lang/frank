{-# LANGUAGE PackageImports, ConstraintKinds #-}
-- A simple parser for the Frank language
module Parser where

import Control.Applicative
import Control.Monad

import Text.Trifecta
import "indentation-trifecta" Text.Trifecta.Indentation

import Data.Char
import Text.Parser.Token as Tok
import qualified Text.Parser.Token.Highlight as Hi
import qualified Data.HashSet as HashSet

import Syntax

type MonadicParsing m = (TokenParsing m, Monad m)

frankStyle :: MonadicParsing m => IdentifierStyle m
frankStyle = IdentifierStyle {
    _styleName = "Frank"
  , _styleStart = satisfy isAlpha
  , _styleLetter = satisfy isAlpha
  , _styleReserved = HashSet.fromList ["data"]
  , _styleHighlight = Hi.Identifier
  , _styleReservedHighlight = Hi.ReservedIdentifier }

identifier :: MonadicParsing m => m String
identifier = Tok.ident langStyle

reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve langStyle

prog :: (Applicative m, MonadicParsing m, IndentationParsing m) => m RawProg
prog = MkRawProg $ many tterm

tterm :: (MonadicParsing m, IndentationParsing m) => m RawTopTm
tterm = MkRawDataTm <$> adt <|>
        MkRawSigTm <$> try parseMHSig <|>
        MkRawDefTm <$> parseMHCls

adt :: (MonadicParsing m, IndentationParsing m) => m AlgDataType
adt = do reserved "data"
         name <- identifier
         symbol "="
         xs <- localIndentation Gt ctrlist
         return (Info (name, xs))

ctrlist :: (MonadicParsing m, IndentationParsing m) => m [Ctr]
ctrlist = sepBy parseCtr (symbol "|")

parseCtr :: MonadicParsing m => m Ctr
parseCtr = do name <- identifier
              args <- many parseVType
              return $ MkCtr name args

parseMHSig :: (MonadicParsing m, IndentationParsing m) => m MHSig
parseMHSig = do name <- identifier
                symbol ":"
                ty <- parseVType
                return (MkSig name ty)

parseMHCls :: (MonadicParsing m, IndentationParsing m) => m MHCls
parseMHCls = do name <- identifier
                ps <- many parsePattern
                symbol "="
                tm <- localIndentation Gt parseTm
                return $ MkMHCls name (MkCls ps tm)

parseCType :: MonadicParsing m => m CType
parseCType = do ports <- many parsePort
                peg <- parsePeg
                return $ MkCType ports peg

parsePort :: MonadicParsing m => m Port
parsePort = do m <- optional $ between (symbol "<") (symbol ">")
                      (sepBy parseAdj' (symbol ","))
               case m of
                 Nothing -> return MkIdAdj
                 Just es -> makeAdj es []

parseEffIns :: MonadicParsing m => m [EffIn]
parseEffIns = do m <- optional $ between (symbol "<") (symbol ">")
                      (sepBy adjustments (symbol ","))
                 case m of
                   Just es -> return es
                   Nothing -> return []                   

parseAdj' :: MonadicParsing m => m Adj
parseAdj' = do x <- identifier
               ts <- many parseVType
               return (MkAdjPlus MkIdAdj x ts)

makeAdj :: [Adj] -> Adj -> Adj
makeAdj ((MkAdjPlus MkIdAdj id ts) : adjs') adj =
  makeAdj adjs' (MkAdjPlus adj id ts)
makeAdj ((MkAdjPlus adj _ _) : _) _ =
  assertParsedOk (Left "identity adjustment") adj
makeAdj [] adj = adj

parseVType :: MonadicParsing m => m VType
parseVType = MkSCTy $ try parseCType <|>
             (do x <- identifier
                 return (MkTVar x))

parseTm :: (MonadicParsing m, IndentationParsing m) => m Tm
parseTm = MkSC <$> parseSComp <|>
          MkDCon <$> try parseDCon <|>
          MkUse <$> parseUse

parseDCon :: (MonadicParsing m, IndentationParsing m) => m DataCon
parseDCon = do k <- identifier
               args <- many parseTm
               return (MkDataCon k args)

parseUse :: (MonadicParsing m, IndentationParsing m) => m Use
parseUse = try parseApp <|> (do x <- identifier
                                return $ MkIdent x)

parseApp :: (MonadicParsing m, IndentationParsing m) => m Use
parseApp = do x <- identifier
              args <- choice [some parseTm, symbol "!" >> pure []]
              return $ MkApp x args

parseClause :: (MonadicParsing m, IndentationParsing m) => m Clause
parseClause = do ps <- sepBy1 identifier (symbol ",")
                 symbol "->"
                 tm <- parseTm
                 return $ MkCls ps tm

parseSComp :: (MonadicParsing m, IndentationParsing m) => m SComp
parseSComp =
  absoluteIndentation $ do cs <- between (symbol "{") (symbol "}") $
                                 sepBy1 parseClause (symbol "|")
                                 return $ MkSComp sc

evalCharIndentationParserT :: Monad m => IndentationParserT Char m a ->
                              IndentationState -> m a
evalCharIndentationParserT = evalIndentationParserT

evalTokenIndentationParserT :: Monad m => IndentationParserT Token m a ->
                               IndentationState -> m a
evalTokenIndentationParserT = evalIndentationParserT

runParse ev input
 = let indA = ev lang $ mkIndentationState 0 infIndentation True Ge
   in case parseString indA mempty input of
    Failure err -> Left (show err)
    Success t -> Right t

runCharParse = runParse evalCharIndentationParserT
runTokenParse = runParse evalTokenIndentationParserT

assertParsedOk :: (Show err, Show a, Eq a) => Either err a -> a -> Assertion
assertParsedOk actual expected =
  case actual of
   Right ok -> assertEqual "parsing succeeded, but " expected ok
   Left err -> assertFailure ("parse failed with " ++ show err
                              ++ ", expected " ++ show expected)
