module Control.Comonad.Store.Memoized.Trans where

import Control.Alt (class Functor, (<$>))
import Control.Category ((<<<))
import Control.Comonad (class Comonad, class Extend, extract)
import Control.Comonad.Store (class ComonadStore)
import Control.Comonad.Trans.Class (class ComonadTrans)
import Control.Extend ((<<=))
import Data.Function (($))
import Data.Function.Memoize (class Tabulate, memoize)
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (type (/\), (/\))


newtype MemoizedStoreT s w a = MemoizedStoreT ((w (s -> a)) /\ s)

runMemoizedStoreT :: forall s w a . MemoizedStoreT s w a -> ((w (s -> a)) /\ s)
runMemoizedStoreT (MemoizedStoreT ctx) = ctx
 
derive instance Newtype (MemoizedStoreT s w a) _

instance
  ( Tabulate s
  , Functor w
  ) => Functor (MemoizedStoreT s w) where
  map f (MemoizedStoreT (w /\ s)) = MemoizedStoreT (((\g -> memoize (f <<< g)) <$> w) /\ s)

instance
  ( Tabulate s
  , Extend w
  ) => Extend (MemoizedStoreT s w) where
  extend f (MemoizedStoreT (w /\ s)) = MemoizedStoreT (((\w' s' -> f (MemoizedStoreT (w' /\ s'))) <<= w) /\ s)

instance
  ( Tabulate s
  , Comonad w
  ) => Comonad (MemoizedStoreT s w) where
  extract (MemoizedStoreT (w /\ a)) = extract w a

instance ComonadTrans (MemoizedStoreT s) where
  lower (MemoizedStoreT (w /\ s)) = (_ $ s) <$> w

instance
  ( Tabulate s
  , Comonad w
  ) => ComonadStore s (MemoizedStoreT s w) where
  pos (MemoizedStoreT (_ /\ s)) = s
  peek s (MemoizedStoreT (f /\ _)) = extract f s

