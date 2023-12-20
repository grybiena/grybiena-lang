module Language.Category.Prim where

import Prelude

import Control.Comonad.Cofree ((:<))
import Data.Maybe (Maybe(..))
import Language.Category.Opaque (Opaque(..))
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Prim as Prim
import Unsafe.Coerce (unsafeCoerce)

newtype Prim :: forall k. k -> Prim.Type
newtype Prim a = Int Prim.Int

instance
  ( Monad m
  , Inject Opaque cat
  ) => Elimination Prim cat typ m where
    elimination (Int i) t = pure $ Just $ t :< inj (Opaque { pretty: show i, term: unsafeCoerce i })


