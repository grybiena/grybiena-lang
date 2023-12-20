module Language.Monad.Context where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (class MonadState, get, modify_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe, maybe)

class Context var typ m where
  assume :: var Void -> typ -> m Unit
  require :: var Void -> m typ
  substitute :: var Void -> typ -> m Unit
  replace :: m (var Void -> Maybe typ)

class Environment var typ c where
  putEnv :: var Void -> typ -> c -> c
  getEnv :: var Void -> c -> Maybe typ

class Substitution var typ c where
  putSub :: var Void -> typ -> c -> c
  getSub :: var Void -> c -> Maybe typ


class NotInScopeError var err where
  notInScopeError :: var Void -> err

instance
  ( Monad m
  , Environment var typ c
  , Substitution var typ c
  , MonadState c m
  , NotInScopeError var e
  , MonadThrow e m
  ) => Context var typ m where
  assume v t = modify_ (putEnv v t)
  require v = do
     e <- get
     maybe (throwError (notInScopeError v)) pure (getEnv v e)
  substitute v t = modify_ (putSub v t)
  replace = do
     e <- get
     pure (flip getSub e)


newtype Ctx var typ =
  Ctx { assumptions :: Map (var Void) typ
      , substitutions :: Map (var Void) typ
      , count :: Int
      , eliminations :: Int
      }

instance
  ( Ord (var Void)
  ) => Environment var typ (Ctx var typ) where 
  putEnv v t (Ctx c) = Ctx (c { assumptions = Map.insert v t c.assumptions })
  getEnv v (Ctx c) = Map.lookup v c.assumptions

instance
  ( Ord (var Void)
  ) => Substitution var typ (Ctx var typ) where 
  putSub v t (Ctx c) = Ctx (c { substitutions = Map.insert v t c.substitutions })
  getSub v (Ctx c) = Map.lookup v c.substitutions

emptyCtx :: forall var typ . Ctx var typ
emptyCtx = Ctx { assumptions: Map.empty, substitutions: Map.empty, count: 0, eliminations: 0 }

