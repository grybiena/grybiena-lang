module Language.Parser.Common where

import Prelude

import Data.Identity (Identity(..))
import Data.List (List)
import Data.Maybe (Maybe(..))
import Parsing (ParserT, mapParserT)
import Parsing.Combinators (choice, optionMaybe)
import Parsing.Indent (IndentParser)
import Parsing.Language (haskellStyle)
import Parsing.Token (GenLanguageDef(..), GenTokenParser, makeTokenParser)

type Parser a = IndentParser String a
 
tokenParser :: GenTokenParser String Identity 
tokenParser = makeTokenParser (let LanguageDef def = haskellStyle
                                in LanguageDef (def { reservedOpNames = [ "=", "::", ",", ".", "\\", "->"]
                                                    , reservedNames = [ "forall", "type", "data", "String", "Int", "_", "log"]
                                                    }))

integer :: forall m . Monad m => ParserT String m Int
integer = mapParserT (\(Identity r) -> pure r) tokenParser.integer 

reservedOp :: forall m. Monad m => String -> ParserT String m Unit
reservedOp s = mapParserT (\(Identity r) -> pure r) (tokenParser.reservedOp s)

commaSep :: forall m a. Monad m => ParserT String Identity a -> ParserT String m (List a)
commaSep s = mapParserT (\(Identity r) -> pure r) (tokenParser.commaSep s)

reserved :: forall m. Monad m => String -> ParserT String m Unit
reserved s = mapParserT (\(Identity r) -> pure r) (tokenParser.reserved s)

identifier :: forall m. Monad m => ParserT String m String
identifier = mapParserT (\(Identity r) -> pure r) tokenParser.identifier

operator :: forall m. Monad m => ParserT String m String
operator = mapParserT (\(Identity r) -> pure r) tokenParser.operator

stringLiteral :: forall m. Monad m => ParserT String m String
stringLiteral = mapParserT (\(Identity r) -> pure r) tokenParser.stringLiteral

lexeme :: forall m a. Monad m => ParserT String Identity a -> ParserT String m a
lexeme s = mapParserT (\(Identity r) -> pure r) (tokenParser.lexeme s)

brackets :: forall m a. Monad m => ParserT String Identity a -> ParserT String m a
brackets s = mapParserT (\(Identity r) -> pure r) (tokenParser.brackets s)

braces :: forall m a. Monad m => ParserT String Identity a -> ParserT String m a
braces s = mapParserT (\(Identity r) -> pure r) (tokenParser.braces s)

parens :: forall m a. Monad m => ParserT String Identity a -> ParserT String m a
parens s = mapParserT (\(Identity r) -> pure r) (tokenParser.parens s)


---
buildPostfixParser :: forall s m a. Array (a -> ParserT s m a) -> ParserT s m a -> ParserT s m a
buildPostfixParser fs first = do
  a <- first
  go a
  where
  go a = do
    maybeA <- optionMaybe $ choice (map (\f -> f a) fs)
    case maybeA of
      Nothing -> pure a
      Just a' -> go a'

