module Language.Parser.Basis where

import Control.Monad (class Monad)
import Data.Either (Either)
import Language.Lambda.Calculus (LambdaF)
import Parsing (ParseError)

class (Monad (t m), Monad m) <= BasisParser t m f var cat where
  parseBasis :: t m (f (LambdaF var cat)) 


class StringParserT t m where
  runStringParserT :: forall a . String -> t m a -> m (Either ParseError a)


