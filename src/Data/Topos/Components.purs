module Data.Topos.Components where

import Data.List (List)

class Components g where
  components :: g -> List g


