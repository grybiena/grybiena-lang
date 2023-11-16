module Language.Parser.Common where

import Prelude

import Control.Alt ((<|>))
import Data.List (List)
import Data.Maybe (Maybe(..))
import Parsing (ParserT)
import Parsing.Combinators (choice, optionMaybe)
import Parsing.Indent (IndentParser)
import Parsing.String.Basic (alphaNum, letter, oneOf)
import Parsing.Token (GenLanguageDef(..), GenTokenParser, makeTokenParser)

type Parser a = IndentParser String a

type LanguageDef m = GenLanguageDef String m

languageDef :: forall m . Array String -> LanguageDef m
languageDef extraReservedNames = LanguageDef 
  { commentStart: "{-"
  , commentEnd: "-}"
  , commentLine: "--"
  , nestedComments: true
  , identStart: letter
  , identLetter: alphaNum <|> oneOf [ '_', '\'' ]
  , opStart: op'
  , opLetter: op'
  , reservedOpNames
  , reservedNames
  , caseSensitive: true
  }
  where
  op' :: ParserT String m Char
  op' = oneOf [ ':', '!', '#', '$', '%', '&', '*', '+', '.', '/', '<', '=', '>', '?', '@', '\\', '^', '|', '-', '~' ]
  reservedOpNames =  [ "=", "::", ",", ".", "\\", "->"]
  reservedNames = [ "forall", "type", "data", "String", "Int", "Number", "Effect" ] <> extraReservedNames

 
tokenParser :: forall m. GenTokenParser String m 
tokenParser = makeTokenParser (languageDef  ["_", "intPlus", "numPlus", "pureEffect", "bindEffect"])

integer :: forall m . Monad m => ParserT String m Int
integer = tokenParser.integer 

number :: forall m . Monad m => ParserT String m Number
number = tokenParser.float

reservedOp :: forall m. Monad m => String -> ParserT String m Unit
reservedOp = tokenParser.reservedOp

commaSep :: forall m a. Monad m => ParserT String m a -> ParserT String m (List a)
commaSep = tokenParser.commaSep

reserved :: forall m. Monad m => String -> ParserT String m Unit
reserved = tokenParser.reserved

identifier :: forall m. Monad m => ParserT String m String
identifier = tokenParser.identifier

operator :: forall m. Monad m => ParserT String m String
operator = tokenParser.operator

stringLiteral :: forall m. Monad m => ParserT String m String
stringLiteral = tokenParser.stringLiteral

lexeme :: forall m a. Monad m => ParserT String m a -> ParserT String m a
lexeme = tokenParser.lexeme

brackets :: forall m a. Monad m => ParserT String m a -> ParserT String m a
brackets = tokenParser.brackets

braces :: forall m a. Monad m => ParserT String m a -> ParserT String m a
braces = tokenParser.braces

parens :: forall m a. Monad m => ParserT String m a -> ParserT String m a
parens = tokenParser.parens


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

