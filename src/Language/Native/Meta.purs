module Language.Native.Meta where

import Prelude

import Control.Monad.Cont (lift)
import Control.Monad.Error.Class (throwError)
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
import Parsing (ParserT, runParserT)
import Parsing.String (eof)
import Prim.RowList (class RowToList)
import Type.Proxy (Proxy)
import Unsafe.Coerce (unsafeCoerce)


metaModule :: forall m mod names het listing.

     HomogeneousRowLabels het (ParserT String m (Native Term)) listing 
  => RowToList mod names 
  => MapRecordWithIndex names MetaNativeTerm mod het 
  => MonadRec m
  => Fresh Int m
  => Record mod
  -> NativeModule listing (ParserT String m (Native Term))
metaModule r = let (x :: Record het) = hmapWithIndex MetaNativeTerm r in homogeneous x 

newtype MetaNative = MetaNative { metaType :: String, nativeTerm :: forall a. a }

data MetaNativeTerm = MetaNativeTerm

instance
  ( IsSymbol sym
  , MonadRec m
  , Fresh Int m
  ) => MappingWithIndex MetaNativeTerm (Proxy sym) MetaNative (ParserT String m (Native Term)) where
  mappingWithIndex MetaNativeTerm = \i t -> metaNative (reflectSymbol i) t



metaNative :: forall m .
              MonadRec m
           => Fresh Int m
           => String -> MetaNative -> ParserT String m (Native Term)
metaNative nativePretty (MetaNative { metaType, nativeTerm }) = do
  t <- lift $ runParserT metaType do
     v <- (parser (nativeModule {})).parseType
     eof
     pure v
  flip (either throwError) t $ \nt -> do
     nativeType <- lift $ renameFresh nt
     pure $ Purescript { nativeType
                       , nativePretty
                       , nativeTerm: unsafeCoerce nativeTerm
                       }

