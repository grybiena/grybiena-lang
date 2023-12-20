module Language.Monad.Fresh where

import Prelude

import Control.Comonad.Cofree (Cofree, (:<))
import Control.Monad.State (class MonadState, modify)
import Data.Functor.Mu (Mu)
import Language.Category.Hole (Hole, hole)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (Ctx(..))
import Matryoshka (class Corecursive, embed)
import Type.Proxy (Proxy(..))


class Fresh :: forall k. k -> (k -> Type) -> Constraint
class Fresh a m where
  fresh :: m a 

class Counter c where
  increment :: c -> c
  count :: c -> Int

instance Counter (Ctx var typ) where
  increment (Ctx c) = Ctx (c { count = c.count + 1 })
  count (Ctx c) = c.count


class Indexable a where
  index :: Int -> a

instance ( MonadState c m, Counter c ) => Fresh Int m where
  fresh = count <$> modify increment 
else
instance
  ( Monad m
  , Indexable i
  , MonadState c m
  , Counter c
  ) => Fresh i m where
  fresh = index <$> fresh


freshHole :: forall var u t m .
             Monad m
          => Fresh (var (Cofree t (Universe u t))) m
          => Corecursive (u (Cofree t)) (Cofree t)
          => Inject Hole t
          => Inject var t
          => Proxy var -> m (Universe u t)
freshHole _ = do
  (v :: var (Cofree t (Universe u t))) <- fresh
  pure (embed ((hole :: Universe u t) :< inj v))



