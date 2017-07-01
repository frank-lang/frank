{-# LANGUAGE PackageImports, ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving,FlexibleInstances #-}

module ParserCommon where

import Text.Trifecta
import Text.Trifecta.Delta
import "indentation-trifecta" Text.Trifecta.Indentation

import Text.Parser.Token as Tok
import Text.Parser.Token.Style
import qualified Text.Parser.Token.Highlight as Hi

import Control.Applicative
import Control.Monad

import Data.Char
import qualified Data.Map.Strict as M
import qualified Data.HashSet as HashSet

newtype FrankParser t m a =
  FrankParser { runFrankParser :: IndentationParserT t m a }
  deriving (Functor, Alternative, Applicative, Monad, Parsing
           , IndentationParsing, MonadPlus)

deriving instance (DeltaParsing m) => (DeltaParsing (FrankParser Token m))
deriving instance (DeltaParsing m) => (CharParsing (FrankParser Char m))
deriving instance (DeltaParsing m) => (CharParsing (FrankParser Token m))
deriving instance (DeltaParsing m) => (TokenParsing (FrankParser Char m))

instance DeltaParsing m => TokenParsing (FrankParser Token m) where
  someSpace = FrankParser $ buildSomeSpaceParser someSpace haskellCommentStyle
  nesting = FrankParser . nesting . runFrankParser
  semi = FrankParser $ runFrankParser semi
  highlight h = FrankParser . highlight h . runFrankParser
  token p = (FrankParser $ token (runFrankParser p)) <* whiteSpace

type MonadicParsing m = (TokenParsing m, IndentationParsing m, Monad m, DeltaParsing m)

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
