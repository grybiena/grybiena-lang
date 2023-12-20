module Language.Monad.Context where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (class MonadState, get, modify_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (class Traversable, traverse)
import Language.Functor.Coproduct (class Inject, prj)
import Language.Functor.Universe (Universe)
import Matryoshka (class Corecursive, class Recursive, embed, project)
import Type.Proxy (Proxy(..))


class Context var typ m where
  assume :: var Unit -> typ -> m Unit
  require :: var Unit -> m typ

class Subtext var typ m where
  substitute :: var Unit -> typ -> m Unit
  replace :: m (var Unit -> Maybe typ)

class Environment var typ c where
  putEnv :: var Unit -> typ -> c -> c
  getEnv :: var Unit -> c -> Maybe typ

class Substitution var typ c where
  putSub :: var Unit -> typ -> c -> c
  getSub :: var Unit -> c -> Maybe typ


class NotInScopeError var err where
  notInScopeError :: var Unit -> err

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

instance
  ( Monad m
  , Substitution var typ c
  , MonadState c m
--  , Rewrite var typ m 
  ) => Subtext var typ m where
  substitute v t = do
--     t' <- rewrite (Proxy :: Proxy var) t
     modify_ (putSub v t)
  replace = do
     e <- get
     pure (flip getSub e)


newtype Ctx var typ =
  Ctx { assumptions :: Map (var Unit) typ
      , substitutions :: Map (var Unit) typ
      , count :: Int
      , eliminations :: Int
      }

instance
  ( Ord (var Unit)
  ) => Environment var typ (Ctx var typ) where 
  putEnv v t (Ctx c) = Ctx (c { assumptions = Map.insert v t c.assumptions })
  getEnv v (Ctx c) = Map.lookup v c.assumptions

instance
  ( Ord (var Unit)
  ) => Substitution var typ (Ctx var typ) where 
  putSub v t (Ctx c) = Ctx (c { substitutions = Map.insert v t c.substitutions })
  getSub v (Ctx c) = Map.lookup v c.substitutions

emptyCtx :: forall var typ . Ctx var typ
emptyCtx = Ctx { assumptions: Map.empty, substitutions: Map.empty, count: 0, eliminations: 0 }


class Rewrite var a m where
  rewrite :: Proxy var -> a -> m a

class Variable var where
  variable :: forall a b. var a -> var b

instance
  ( Inject var t
  , Recursive (u (Cofree t)) (Cofree t) 
  , Corecursive (u (Cofree t)) (Cofree t) 
  , Monad m
  , Traversable t
  , Subtext var (Universe u t) m
  ) => Rewrite var (Universe u t) m where
  rewrite _ t = do
    let q :: t (Cofree t (Universe u t))
        q = (tail $ project t)
    case prj q of
      Just v -> do
        (r :: var _ -> Maybe (Universe u t)) <- replace
        case r (void v) of
          Nothing -> do
            pure t 
          Just so -> pure so
      Nothing -> do
         -- TODO rewrite the higher levels, terminating appropriately
         (q' :: t (Cofree t (Universe u t))) <- map project <$> traverse (rewrite (Proxy :: Proxy var)) (embed <$> q)
         pure (embed (head (project t) :< q'))

