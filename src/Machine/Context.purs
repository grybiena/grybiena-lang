module Machine.Context where

import Prelude

import Control.Comonad.Store.Class (peek, pos)
import Control.Comonad.Store.Memoized (MemoizedStore, memoizedStore)
import Control.Extend (extend)
import Data.Function.Memoize (class Tabulate)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))

class Context idx obj ctx | ctx -> idx, ctx -> obj where
  empty :: ctx
  binds :: idx -> obj -> ctx -> ctx
  bound :: idx -> ctx -> (Maybe obj)

instance Ord idx => Context idx obj (Map idx obj) where
  empty = Map.empty
  binds idx obj ctx = Map.insert idx obj ctx
  bound idx ctx = Map.lookup idx ctx

instance
  ( Semiring idx
  , Eq idx
  , Tabulate idx
  ) => Context idx obj (MemoizedStore idx (Maybe obj)) where
  empty = memoizedStore (const Nothing) zero
  binds idx obj ctx = extend (\cur -> if pos cur == idx then Just obj else peek (pos cur) cur) ctx 
  bound idx ctx = peek idx ctx


