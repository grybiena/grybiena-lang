module Data.Topos.Pointed where

import Control.Category (identity)
import Data.Set (Set)

class Pointed f o | f -> o where
  points :: f -> Set o 

instance Pointed (Set o) o where
  points = identity


