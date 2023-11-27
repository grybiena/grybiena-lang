module Data.Graph.Edge where

import Prelude

import Data.Relation.Invert (class Invert)
import Data.Set as Set
import Data.Topos.Pointed (class Pointed)
import Data.Tuple.Nested (type (/\), (/\))

newtype Edge v = Edge (v /\ v)
derive newtype instance Eq v => Eq (Edge v)
derive newtype instance Show v => Show (Edge v)

instance Ord v => Pointed (Edge v) v where
  points (Edge (a /\ b)) = Set.fromFoldable [a,b]

instance Invert (Edge v) where
  invert (Edge (a /\ b)) = Edge (b /\ a)


