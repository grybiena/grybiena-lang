module Machine.Context where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)

class Context idx obj ctx where
  empty :: ctx idx obj
  binds :: idx -> obj -> ctx idx obj -> ctx idx obj
  bound :: idx -> ctx idx obj -> (Maybe obj)

instance Ord idx => Context idx obj Map where
  empty = Map.empty
  binds idx obj ctx = Map.insert idx obj ctx
  bound idx ctx = Map.lookup idx ctx

--instance
--  ( Semiring idx
--  , Eq idx
--  , Tabulate idx
--  ) => Context idx obj (MemoizedStore idx (Maybe obj)) where
--  empty = memoizedStore (const Nothing) zero
--  binds idx obj ctx = extend (\cur -> if pos cur == idx then Just obj else peek (pos cur) cur) ctx 
--  bound idx ctx = peek idx ctx


