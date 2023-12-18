module Language.Category.Context where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (class MonadState, get, modify_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe, maybe)

class Context var typ m where
  assume :: var Void -> typ -> m Unit
  require :: var Void -> m typ

class Environment var typ c where
  putEnv :: var Void -> typ -> c -> c
  getEnv :: var Void -> c -> Maybe typ

class NotInScopeError var err where
  notInScopeError :: var Void -> err

instance
  ( Monad m
  , Environment var typ c
  , MonadState c m
  , NotInScopeError var e
  , MonadThrow e m
  ) => Context var typ m where
  assume v t = modify_ (putEnv v t)
  require v = do
     e <- get
     maybe (throwError (notInScopeError v)) pure (getEnv v e)


newtype Ctx var typ = Ctx { ctx :: Map (var Void) typ, count :: Int }

instance
  ( Ord (var Void)
  ) => Environment var typ (Ctx var typ) where 
  putEnv v t (Ctx c) = Ctx (c { ctx = Map.insert v t c.ctx })
  getEnv v (Ctx c) = Map.lookup v c.ctx

emptyCtx :: forall var typ . Ctx var typ
emptyCtx = Ctx { ctx: Map.empty, count: 0 }

