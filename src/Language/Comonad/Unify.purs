module Language.Comonad.Unify where

import Prelude

import Control.Comonad (class Comonad, extract)
import Control.Comonad.Store (StoreT(..))
import Control.Comonad.Store.Class (class ComonadStore, pos, seeks)
import Control.Extend (class Extend, extend)
import Data.Tuple.Nested ((/\))


class
  ( Semiring s
  , ComonadStore s w
  ) <= Fresh s w where
  fresh :: forall a. w a -> s

instance
  ( Semiring s
  , ComonadStore s w
  ) => Fresh s w where 
  fresh = pos <<< seeks (add one)

class Context s w t where
  assume :: StoreT s w t -> s -> t -> StoreT s w t
  require :: StoreT s w t -> s -> t

instance
  ( Extend w
  , Comonad w
  , Eq s
  ) => Context s w t where 
  assume w s t = extend (\(StoreT (f /\ p)) -> if p == s then t else (extract f) s) w
  require (StoreT (f /\_)) = extract f


