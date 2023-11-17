module Language.Parser.Class where

import Control.Monad (class Monad)
import Language.Term (Term)

class Monad m <= Parser m where
  parseTerm :: String -> m Term
  parseType :: String -> m Term
