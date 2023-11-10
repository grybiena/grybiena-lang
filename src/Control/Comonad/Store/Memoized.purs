module Control.Comonad.Store.Memoized where

import Control.Comonad.Store.Memoized.Trans (MemoizedStoreT(..))
import Data.Identity (Identity(..))
import Data.Tuple.Nested (type (/\), (/\))

type MemoizedStore s = MemoizedStoreT s Identity

runMemoizedStore :: forall s a. MemoizedStore s a -> (s -> a) /\ s 
runMemoizedStore (MemoizedStoreT (Identity f /\ s)) = f /\ s

memoizedStore :: forall s a. (s -> a) -> s -> MemoizedStore s a
memoizedStore f s = MemoizedStoreT (Identity f /\ s)



