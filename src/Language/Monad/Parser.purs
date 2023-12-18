module Language.Monad.Parser where

import Prelude

import Data.Foldable (class Foldable)
import Data.Maybe (Maybe)
import Language.Parser.Common (languageDef)
import Parsing (ParserT)
import Parsing as Parsing
import Parsing.Combinators as Combinators
import Parsing.Token (makeTokenParser)

class Monad m <= Parser m where
  reserved :: String -> m Unit
  reservedOp :: String -> m Unit
  identifier :: m String

  try :: forall a. m a -> m a
  fail :: forall a. String -> m a
  optionMaybe :: forall a. m a -> m (Maybe a) 
  choice :: forall f a. Foldable f => f (m a) -> m a

instance Parser (ParserT String m) where
  reserved = (makeTokenParser (languageDef [])).reserved
  reservedOp = (makeTokenParser (languageDef [])).reservedOp
  identifier = (makeTokenParser (languageDef [])).identifier 

  try = Combinators.try
  fail = Parsing.fail 
  optionMaybe = Combinators.optionMaybe
  choice = Combinators.choice
