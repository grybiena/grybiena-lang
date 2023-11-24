module Language.Native.Unsafe where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Either (either)
import Data.Foldable (class Foldable)
import Data.Homogeneous (class HomogeneousRowLabels)
import Data.Homogeneous.Record (homogeneous)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Heterogeneous.Mapping (class MapRecordWithIndex, class MappingWithIndex, hmapWithIndex)
import Language.Lambda.Calculus (class Shadow, LambdaF)
import Language.Lambda.Unification (class Fresh, renameFresh)
import Language.Native (Native(..))
import Language.Native.Module (NativeModule)
import Language.Parser.Basis (class StringParserT, class BasisParser, parseBasis, runStringParserT)
import Matryoshka (class Corecursive, class Recursive)
import Parsing (ParseError)
import Prim.RowList (class RowToList)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)


unsafeModule :: forall t f var cat m mod names het listing.

     HomogeneousRowLabels het (m (Native (f (LambdaF var cat)))) listing 
  => RowToList mod names 
  => MapRecordWithIndex names (UnsafeNativeTerm t) mod het 
  => MonadRec m
  => Fresh Int m
  => Proxy t
  -> Record mod
  -> NativeModule listing (m (Native (f (LambdaF var cat))))
unsafeModule _ r = let (x :: Record het) = hmapWithIndex (UnsafeNativeTerm :: UnsafeNativeTerm t) r in homogeneous x 

newtype UnsafeNative (unsafeType :: Symbol) = UnsafeNative (forall a. a)

data UnsafeNativeTerm :: forall k. k -> Type
data UnsafeNativeTerm t = UnsafeNativeTerm 

instance
  ( IsSymbol sym
  , IsSymbol typ
  , MonadRec m
  , MonadThrow ParseError m
  , Fresh Int m
  , Fresh var m
  , Ord var
  , Shadow var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , BasisParser t m f var cat
  , StringParserT t m
  ) => MappingWithIndex (UnsafeNativeTerm t) (Proxy sym) (UnsafeNative typ) (m (Native (f (LambdaF var cat)))) where
  mappingWithIndex UnsafeNativeTerm = \i t -> unsafeNative (Proxy :: Proxy t) (reflectSymbol i) t



unsafeNative :: forall typ f var cat t m .
              MonadRec m
           => MonadThrow ParseError m
           => Fresh Int m
           => Fresh var m
           => IsSymbol typ
           => Ord var
           => Shadow var
           => Foldable cat
           => Recursive (f (LambdaF var cat)) (LambdaF var cat)
           => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
           => BasisParser t m f var cat
           => StringParserT t m
           => Proxy t
           -> String
           -> UnsafeNative typ
           -> m (Native (f (LambdaF var cat)))
unsafeNative _ nativePretty (UnsafeNative nativeTerm) = do
  t <- runStringParserT (reflectSymbol (Proxy :: Proxy typ)) (parseBasis :: t m (f (LambdaF var cat)))
  flip (either throwError) t $ \nt -> do
     nativeType <- renameFresh nt
     pure $ Purescript { nativeType
                       , nativePretty
                       , nativeTerm: unsafeCoerce nativeTerm
                       }

