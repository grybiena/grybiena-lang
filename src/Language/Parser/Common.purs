module Language.Parser.Common where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (Maybe(..))
import Parsing (ParserT)
import Parsing.Combinators (choice, optionMaybe)
import Parsing.Indent (IndentParser)
import Parsing.String.Basic (alphaNum, letter, oneOf)
import Parsing.Token (GenLanguageDef(..))

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
  reservedNames = [ "forall", "let", "in", "if", "then", "else", "case", "of", "type", "data", "String", "Int", "Number", "Effect" ] <> extraReservedNames

 

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

