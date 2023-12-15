module Language.Lambda.Basis where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Control.Comonad.Cofree (Cofree, (:<))
import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState)
import Data.Foldable (class Foldable)
import Data.Homogeneous.Record (fromHomogeneous)
import Language.Kernel.Basis (basis)
import Language.Lambda.Calculus (class AllVars, class Shadow, LambdaF(..))
import Language.Lambda.Unification (class Fresh, TypingContext)
import Language.Native (class NativeValue, Native(..), nativeCat)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Basis (class StringParserT, class BasisParser)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive)
import Parsing (ParseError)
import Type.Proxy (Proxy)


class (Monad (t m), Monad m) <= Basis t m f var cat where
  basisS :: Proxy t -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat))) 
  basisK :: Proxy t -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat))) 
  basisI :: Proxy t -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat))) 
  basisC :: Proxy t -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat))) 
  basisB :: Proxy t -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat))) 


instance
  ( MonadRec m
  , MonadThrow ParseError m
  , MonadState (TypingContext f var cat) m
  , NativeValue f var cat
  , Fresh var m
  , Ord var
  , Shadow var
  , Foldable cat
  , Recursive (f (LambdaF var var cat)) (LambdaF var var cat)
  , Corecursive (f (LambdaF var var cat)) (LambdaF var var cat)
  , BasisParser t m f var cat
  , StringParserT t m
  , AllVars var var cat
  ) => Basis t m f var cat where
  basisS p = typedNative <$> (fromHomogeneous (unsafeModule p basis))."S"
  basisK p = typedNative <$> (fromHomogeneous (unsafeModule p basis))."K"
  basisI p = typedNative <$> (fromHomogeneous (unsafeModule p basis))."I"
  basisC p = typedNative <$> (fromHomogeneous (unsafeModule p basis))."C"
  basisB p = typedNative <$> (fromHomogeneous (unsafeModule p basis))."B"

typedNative :: forall var cat f .
               NativeValue f var cat
            => Native (f (LambdaF var var cat))
            -> Cofree (LambdaF var var cat) (f (LambdaF var var cat))
typedNative p@(Purescript n) = n.nativeType :< Cat (nativeCat p)

