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

