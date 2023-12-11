module Language.Native.Reify where

import Prelude

import Data.Homogeneous (class HomogeneousRowLabels)
import Data.Homogeneous.Record (homogeneous)
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Heterogeneous.Mapping (class MapRecordWithIndex, class MappingWithIndex, hmapWithIndex)
import Language.Kernel.Data (Data(..))
import Language.Lambda.Calculus (app, cat)
import Language.Native (Native(..))
import Language.Native.Module (NativeModule)
import Language.Term (TT(..), Term)
import Prim (Array, Boolean, Constraint, Int, Number, Record, String)
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
else
instance (Reify a, Reify b) => Reify (a b) where
  reify _ = app (reify (Proxy :: Proxy a)) (reify (Proxy :: Proxy b))

instance Reify (->) where
  reify _ = cat Arrow

instance Reify Effect where
  reify _ = cat (Native (nativeTerm "Effect" primitiveTypeConstructors."Effect"))

instance Reify Int where
  reify _ = cat (Native (nativeTerm "Int" primitiveTypeConstructors."Int"))

instance Reify Number where
  reify _ = cat (Native (nativeTerm "Number" primitiveTypeConstructors."Number"))

instance Reify Boolean where
  reify _ = cat (Native (nativeTerm "Boolean" primitiveTypeConstructors."Boolean"))

instance Reify Maybe where
  reify _ = cat (Native (nativeTerm "Maybe" primitiveTypeConstructors."Maybe"))

instance Reify Array where
  reify _ = cat (Native (nativeTerm "Array" primitiveTypeConstructors."Array"))

type Type = Data Term

primitiveTypeConstructors :: Record 
  ( "Int" :: Type
  , "Number" :: Type
  , "Boolean" :: Type
  , "Effect" :: Type -> Type
  , "Maybe" :: Type -> Type
  , "Array" :: Type -> Type
  )
primitiveTypeConstructors = 
  { "Int": DataConstructor "Int" (Just $ reify (Proxy :: Proxy Type))
  , "Number": DataConstructor "Number" (Just $ reify (Proxy :: Proxy Type))
  , "Boolean": DataConstructor "Boolean" (Just $ reify (Proxy :: Proxy Type))
  , "Effect": DataApp (DataConstructor "Effect" (Just $ reify (Proxy :: Proxy (Type -> Type))))
  , "Maybe": DataApp (DataConstructor "Maybe" (Just $ reify (Proxy :: Proxy (Type -> Type)))) 
  , "Array": DataApp (DataConstructor "Array" (Just $ reify (Proxy :: Proxy (Type -> Type))))
 
  }

