module Language.Parser where

import Control.Alt (class Alt)
import Data.Unit (Unit)

class Alt m <= LanguageParser m where
  reserved :: String -> m Unit
  reservedOp :: String -> m Unit
  try :: forall a. m a -> m a
  fail :: forall a. String -> m a
  identifier :: m String
