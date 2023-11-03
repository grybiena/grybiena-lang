module Language.Parser.Names where

import Prelude

import Data.Array (head)
import Data.CodePoint.Unicode (isUpper)
import Data.Maybe (Maybe(..))
import Data.String (codePointFromChar)
import Data.String.CodeUnits (toCharArray)
import Language.Names (Ident(..), ProperName(..))
import Language.Parser.Common (Parser, identifier, operator)
import Parsing (fail)
import Parsing.Combinators (choice)


properName :: Parser ProperName
properName = do
  i <- identifier
  if Just true == ((isUpper <<< codePointFromChar) <$> head (toCharArray i)) 
    then pure $ ProperName i
    else fail "Proper names must begin with upper case char"

ident :: Parser Ident
ident = choice [parseOp,parseIdent]
  where
    parseOp = Op <$> operator
    parseIdent = do
      i <- identifier
      if Just true == ((not <<< isUpper <<< codePointFromChar) <$> head (toCharArray i)) 
        then pure $ Ident i
        else fail "Identifiers must begin with lower case char"



