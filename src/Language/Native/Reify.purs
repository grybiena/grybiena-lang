module Language.Native.Reify where

import Control.Alternative (class Applicative, pure)
import Data.Homogeneous (class HomogeneousRowLabels)
import Data.Homogeneous.Record (homogeneous)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Heterogeneous.Mapping (class MapRecordWithIndex, class MappingWithIndex, hmapWithIndex)
import Language.Lambda.Calculus (app, cat)
import Language.Native.Module (NativeModule)
import Language.Term (TT(..), Term)
import Language.Type (Type, primitiveTypeConstructors)
import Language.Native (Native(..))
import Prim (Constraint, Int, Number, Record, String)
import Prim.RowList (class RowToList)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

nativeModule :: forall m mod names het listing.
     Applicative m
  => HomogeneousRowLabels het (m (Native Term)) listing 
  => RowToList mod names 
  => MapRecordWithIndex names NativeTerm mod het 
  => Record mod 
  -> NativeModule listing (m (Native Term))
nativeModule r = let (x :: Record het) = hmapWithIndex NativeTerm r in homogeneous x 

data NativeTerm = NativeTerm

instance (Reify native, IsSymbol sym, Applicative m) => MappingWithIndex NativeTerm (Proxy sym) native (m (Native Term)) where
  mappingWithIndex NativeTerm = \i t -> pure (nativeTerm (reflectSymbol i) t)

nativeTerm :: forall t . Reify t => String -> t -> Native Term
nativeTerm nativePretty term = Purescript
  { nativeType: reify (Proxy :: Proxy t)
  , nativePretty
  , nativeTerm: unsafeCoerce term
  }


class Reify :: forall k. k -> Constraint
class Reify s where
  reify :: Proxy s -> Term

instance Reify Type where
  reify _ = cat (Star 1)

instance Reify (->) where
  reify _ = cat Arrow

instance (Reify a, Reify b) => Reify (a b) where
  reify _ = app (reify (Proxy :: Proxy a)) (reify (Proxy :: Proxy b))

instance Reify Effect where
  reify _ = cat (Native (nativeTerm "Effect" primitiveTypeConstructors."Effect"))

instance Reify Int where
  reify _ = cat (Native (nativeTerm "Int" primitiveTypeConstructors."Int"))

instance Reify Number where
  reify _ = cat (Native (nativeTerm "Number" primitiveTypeConstructors."Number"))


