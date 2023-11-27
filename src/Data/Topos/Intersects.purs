module Data.Topos.Intersects where

import Prelude

import Data.Foldable (null)
import Data.Set as Set
import Data.Topos.Pointed (class Pointed, points)

class Intersects a b where
  intersects :: a -> b -> Boolean


instance (Pointed a o, Pointed b o, Ord o) => Intersects a b where
  intersects a b = not $ null $ Set.intersection (points a) (points b) 


