module Language.Lambda.Basis where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState)
import Data.Foldable (class Foldable)
import Data.Homogeneous.Record (fromHomogeneous)
import Language.Kernel.Basis (basis)
import Language.Lambda.Calculus (class Shadow, LambdaF)
import Language.Lambda.Unification (class Fresh, TypingContext)
import Language.Native (class NativeValue, native)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Basis (class StringParserT, class BasisParser)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive)
import Parsing (ParseError)
import Type.Proxy (Proxy)


class (Monad (t m), Monad m) <= Basis t m f var cat where
  basisS :: Proxy t -> m (f (LambdaF var cat)) 
  basisK :: Proxy t -> m (f (LambdaF var cat)) 
  basisI :: Proxy t -> m (f (LambdaF var cat)) 
  basisC :: Proxy t -> m (f (LambdaF var cat)) 
  basisB :: Proxy t -> m (f (LambdaF var cat)) 


instance
  ( MonadRec m
  , MonadThrow ParseError m
  , MonadState (TypingContext var f var cat) m
  , NativeValue f var cat
  , Fresh var m
  , Ord var
  , Shadow var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , BasisParser t m f var cat
  , StringParserT t m
  ) => Basis t m f var cat where
  basisS p = native <$> (fromHomogeneous (unsafeModule p basis))."S"
  basisK p = native <$> (fromHomogeneous (unsafeModule p basis))."K"
  basisI p = native <$> (fromHomogeneous (unsafeModule p basis))."I"
  basisC p = native <$> (fromHomogeneous (unsafeModule p basis))."C"
  basisB p = native <$> (fromHomogeneous (unsafeModule p basis))."B"

