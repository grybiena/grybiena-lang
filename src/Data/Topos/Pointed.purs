module Data.Topos.Pointed where

import Prelude

import Data.List (List, fold)
import Data.Set (Set)

class Pointed f o | f -> o where
  points :: f -> Set o 

instance Pointed (Set o) o where
  points = identity

instance (Pointed a o, Ord o) => Pointed (List a) o where 
  points = fold <<< map points
