module Language.Category.Context where

import Data.Unit (Unit)
import Data.Void (Void)

class Context var typ m where
  assume :: var Void -> typ -> m Unit
  require :: var Void -> m typ


