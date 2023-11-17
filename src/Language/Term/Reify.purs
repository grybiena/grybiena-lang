module Language.Term.Reify where

import Control.Alternative (class Applicative, pure)
import Control.Category ((<<<))
import Data.Homogeneous (class HomogeneousRowLabels)
import Data.Homogeneous.Record (homogeneous)
import Effect (Effect)
import Heterogeneous.Mapping (class MapRecordWithIndex, class Mapping, ConstMapping, hmap)
import Language.Lambda.Calculus (app, cat)
import Language.Module (Module)
import Language.Term (TT(..), Term)
import Language.Value.Native (Native(..))
import Prim.RowList (class RowToList)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

nativeModule :: forall m mod names het listing.
     Applicative m
  => HomogeneousRowLabels het (m (Native Term)) listing 
  => RowToList mod names 
  => MapRecordWithIndex names (ConstMapping NativeTerm) mod het 
  => Record mod 
  -> Module listing (m (Native Term))
nativeModule r = let (x :: Record het) = hmap NativeTerm r in homogeneous x 


data NativeTerm = NativeTerm

instance (Reify native, Applicative m) => Mapping NativeTerm native (m (Native Term)) where
  mapping NativeTerm = pure <<< nativeTerm

nativeTerm :: forall t . Reify t => t -> Native Term
nativeTerm term = Purescript
  { nativeType: reify (Proxy :: Proxy t)
  , nativeTerm: unsafeCoerce term
  }


class Reify :: forall k. k -> Constraint
class Reify s where
  reify :: Proxy s -> Term

instance Reify (->) where
  reify _ = cat Arrow

instance Reify Effect where
  reify _ = cat TypeEffect

instance Reify Int where
  reify _ = cat TypeInt

instance Reify Number where
  reify _ = cat TypeNumber

instance (Reify a, Reify b) => Reify (a b) where
  reify _ = app (reify (Proxy :: Proxy a)) (reify (Proxy :: Proxy b))

