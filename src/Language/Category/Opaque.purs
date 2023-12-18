module Language.Category.Opaque where

import Prelude

import Control.Comonad.Cofree ((:<))
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Coproduct (class Inject, inj)
import Unsafe.Coerce (unsafeCoerce)


newtype Opaque :: forall k. k -> Type
newtype Opaque a = Opaque { pretty :: String, term :: forall x. x }

instance Functor Opaque where
  map _ (Opaque o) = Opaque o

instance
  ( Monad m
  , Inject Opaque cat
  ) => Elimination Opaque cat typ m where
    elimination (Opaque { term }) t = pure $ t :< inj (Opaque (unsafeCoerce term))


