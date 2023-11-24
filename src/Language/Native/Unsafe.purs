module Language.Native.Unsafe where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Either (either)
import Data.Homogeneous (class HomogeneousRowLabels)
import Data.Homogeneous.Record (homogeneous)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Heterogeneous.Mapping (class MapRecordWithIndex, class MappingWithIndex, hmapWithIndex)
import Language.Lambda.Unification (class Fresh, renameFresh)
import Language.Native (Native(..))
import Language.Native.Module (NativeModule)
import Language.Native.Reify (nativeModule)
import Language.Parser.Term (parser)
import Language.Term (Term)
import Parsing (ParseError, runParserT)
import Parsing.String (eof)
import Prim.RowList (class RowToList)
import Type.Proxy (Proxy)
import Unsafe.Coerce (unsafeCoerce)


unsafeModule :: forall m mod names het listing.

     HomogeneousRowLabels het (m (Native Term)) listing 
  => RowToList mod names 
  => MapRecordWithIndex names UnsafeNativeTerm mod het 
  => MonadRec m
  => Fresh Int m
  => Record mod
  -> NativeModule listing (m (Native Term))
unsafeModule r = let (x :: Record het) = hmapWithIndex UnsafeNativeTerm r in homogeneous x 

newtype UnsafeNative = UnsafeNative { unsafeType :: String, nativeTerm :: forall a. a }

data UnsafeNativeTerm = UnsafeNativeTerm

instance
  ( IsSymbol sym
  , MonadRec m
  , MonadThrow ParseError m
  , Fresh Int m
  ) => MappingWithIndex UnsafeNativeTerm (Proxy sym) UnsafeNative (m (Native Term)) where
  mappingWithIndex UnsafeNativeTerm = \i t -> unsafeNative (reflectSymbol i) t



unsafeNative :: forall m .
              MonadRec m
           => MonadThrow ParseError m
           => Fresh Int m
           => String -> UnsafeNative -> m (Native Term)
unsafeNative nativePretty (UnsafeNative { unsafeType, nativeTerm }) = do
  t <- runParserT unsafeType do
     v <- (parser (nativeModule {})).parseType
     eof
     pure v
  flip (either throwError) t $ \nt -> do
     nativeType <- renameFresh nt
     pure $ Purescript { nativeType
                       , nativePretty
                       , nativeTerm: unsafeCoerce nativeTerm
                       }

