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
import Matryoshka (class Corecursive, class Recursive)
import Parsing (ParseError, ParserT, runParserT)
import Parsing.String (eof)
import Prim.RowList (class RowToList)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)


unsafeModule :: forall f var cat m mod names het listing.

     HomogeneousRowLabels het (m (Native (f (LambdaF var cat)))) listing 
  => RowToList mod names 
  => MapRecordWithIndex names (UnsafeNativeTerm f var cat m) mod het 
  => MonadRec m
  => Fresh Int m
  => ParserT String m (f (LambdaF var cat))
  -> Record mod
  -> NativeModule listing (m (Native (f (LambdaF var cat))))
unsafeModule p r = let (x :: Record het) = hmapWithIndex (UnsafeNativeTerm p) r in homogeneous x 

newtype UnsafeNative (unsafeType :: Symbol) = UnsafeNative (forall a. a)

data UnsafeNativeTerm f var cat m = UnsafeNativeTerm (ParserT String m (f (LambdaF var cat)))

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
  ) => MappingWithIndex (UnsafeNativeTerm f var cat m) (Proxy sym) (UnsafeNative typ) (m (Native (f (LambdaF var cat)))) where
  mappingWithIndex (UnsafeNativeTerm p) = \i t -> unsafeNative p (reflectSymbol i) t



unsafeNative :: forall typ f var cat m .
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
           => ParserT String m (f (LambdaF var cat))
           -> String
           -> UnsafeNative typ
           -> m (Native (f (LambdaF var cat)))
unsafeNative parseType nativePretty (UnsafeNative nativeTerm) = do
  t <- runParserT (reflectSymbol (Proxy :: Proxy typ)) do
     v <- parseType
     eof
     pure v
  flip (either throwError) t $ \nt -> do
     nativeType <- renameFresh nt
     pure $ Purescript { nativeType
                       , nativePretty
                       , nativeTerm: unsafeCoerce nativeTerm
                       }

