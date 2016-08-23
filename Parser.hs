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
identifier = Tok.ident frankStyle

reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve frankStyle

prog :: (Applicative m, MonadicParsing m, IndentationParsing m) => m RawProg
prog = MkRawProg <$> many tterm

tterm :: (MonadicParsing m, IndentationParsing m) => m RawTopTm
tterm = MkRawDataTm <$> parseDataT <|>
        MkRawSigTm <$> try parseMHSig <|>
        MkRawDefTm <$> parseMHCls

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
               let port = (case m of
                              Nothing -> MkIdAdj
                              Just es -> makeAdj es MkIdAdj)
               ty <- parseVType
               return $ MkPort port ty

parsePeg :: MonadicParsing m => m Peg
parsePeg = do m <- optional $ between (symbol "<") (symbol ">")
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
parseVType = MkSCTy <$> try parseCType <|>
             MkTVar <$> identifier

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
parseClause = do ps <- sepBy1 (parseVPat >>= return . MkVPat) (symbol ",")
                 symbol "->"
                 tm <- parseTm
                 return $ MkCls ps tm

parsePattern :: MonadicParsing m => m Pattern
parsePattern = parseCPat <|> MkVPat <$> parseVPat

parseCPat :: MonadicParsing m => m Pattern
parseCPat = do symbol "<"
               x <- identifier
               symbol ">"
               return (MkThkPat x)

parseVPat :: MonadicParsing m => m ValuePat
parseVPat = parseDataTPat <|> (do x <- identifier
                                  return $ MkVarPat x)

parseDataTPat :: MonadicParsing m => m ValuePat
parseDataTPat = between (symbol ")") (symbol ")") $ do k <- identifier
                                                       ps <- many parseVPat
                                                       return $ MkDataPat k ps

parseSComp :: (MonadicParsing m, IndentationParsing m) => m SComp
parseSComp =
  absoluteIndentation $ do cs <- between (symbol "{") (symbol "}") $
                                 sepBy1 parseClause (symbol "|")
                           return $ MkSComp cs

evalCharIndentationParserT :: Monad m => IndentationParserT Char m a ->
                              IndentationState -> m a
evalCharIndentationParserT = evalIndentationParserT

evalTokenIndentationParserT :: Monad m => IndentationParserT Token m a ->
                               IndentationState -> m a
evalTokenIndentationParserT = evalIndentationParserT

runParseFromFileEx ev fname =
  let indA = ev prog $ mkIndentationState 0 infIndentation True Ge in
  do res <- parseFromFileEx indA fname
     case res of
       Failure err -> print err
       Success t -> print $ "Parsing " ++ (show fname) ++ " succeeded!"

runCharParse = runParseFromFileEx evalCharIndentationParserT
runTokenParse = runParseFromFileEx evalTokenIndentationParserT
