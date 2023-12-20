module Language.Category.Opaque where

import Prelude

import Data.Maybe (Maybe(..))
import Language.Functor.Coproduct (class Inject)
import Language.Functor.Elimination (class Elimination)


newtype Opaque :: forall k. k -> Type
newtype Opaque a = Opaque { pretty :: String, term :: forall x. x }

instance Functor Opaque where
  map _ (Opaque o) = Opaque o

instance
  ( Monad m
  , Inject Opaque cat
  ) => Elimination Opaque cat typ m where
    elimination _ _ = pure Nothing 


