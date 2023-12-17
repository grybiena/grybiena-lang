module Language.Functor.Value.Var where

import Prelude

import Control.Comonad.Cofree ((:<))
import Language.Category.Elimination (class Elimination)
import Language.Category.Inference (class Inference)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Lambda.Unification (class Context, require)

newtype Var :: forall k. Type -> k -> Type
newtype Var var a = Var var

instance
  ( Monad m
  , Context var typ m
  , Inject (Var var) cat 
  ) => Inference (Var var) cat typ m where
    inference (Var v) = require v >>= \t -> pure (t :< inj (Var v)) 

instance 
  ( Monad m
  , Inject (Var var) cat
  ) => Elimination (Var var) cat typ m where
    elimination v t = pure (t :< inj v)

