module Language.Parser.Class where

import Control.Monad (class Monad)
import Data.Either (Either)
import Language.Lambda.Calculus (LambdaF)
import Parsing (ParseError)

class (Monad (t m), Monad m) <= TypeParser t m f var cat where
  parseType :: t m (f (LambdaF var cat)) 


class StringParserT t m where
  runStringParserT :: forall a . String -> t m a -> m (Either ParseError a)


