module Language.Parser where

import Prelude

import Language.Parser.Common (languageDef)
import Parsing (ParserT)
import Parsing as Parsing
import Parsing.Combinators as Combinators
import Parsing.Token (makeTokenParser)

class Monad m <= Parser m where
  reserved :: String -> m Unit
  reservedOp :: String -> m Unit
  try :: forall a. m a -> m a
  fail :: forall a. String -> m a
  identifier :: m String

instance Parser (ParserT String m) where
  reserved = (makeTokenParser (languageDef [])).reserved
  reservedOp = (makeTokenParser (languageDef [])).reservedOp
  try = Combinators.try
  fail = Parsing.fail 
  identifier = (makeTokenParser (languageDef [])).identifier 

