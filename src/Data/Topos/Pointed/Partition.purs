module Data.Topos.Pointed.Partition where

import Data.List (List)
import Data.Set (Set)

 
class Partition g o where
  partition :: g -> List (Set o)

