module Language.Functor.Elimination where

import Prelude

import Control.Comonad.Cofree (Cofree)
import Control.Monad.State (class MonadState, gets, modify_)
import Data.Maybe (Maybe)
import Language.Monad.Context (Ctx(..))
import Language.Functor.Coproduct (type (:+:), Coproduct(..))

class Elimination obj cat typ m where
  elimination :: obj (Cofree cat typ) -> typ -> m (Maybe (Cofree cat typ))

instance
  ( Elimination a cat typ m
  , Elimination b cat typ m
  ) => Elimination (a :+: b) cat typ m where
    elimination (Inl a) = elimination a
    elimination (Inr b) = elimination b

class Eliminated m where
  eliminated :: m Unit
  eliminations :: m Int

instance
  ( MonadState (Ctx v t) m
  ) => Eliminated m where
  eliminated = modify_ (\(Ctx c) -> Ctx (c { eliminations = c.eliminations + 1 }))
  eliminations = gets (\(Ctx c) -> c.eliminations)

