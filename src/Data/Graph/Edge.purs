module Data.Graph.Edge where

import Prelude

import Data.Relation.Invert (class Invert)
import Data.Set as Set
import Data.Topos.Components (class Components)
import Data.Topos.Pointed (class Pointed, points)
import Data.Topos.Pointed.Partition (class Partition)
import Data.Tuple.Nested (type (/\), (/\))

newtype Edge v = Edge (v /\ v)
derive newtype instance Eq v => Eq (Edge v)
derive newtype instance Show v => Show (Edge v)

instance Ord v => Pointed (Edge v) v where
  points (Edge (a /\ b)) = Set.fromFoldable [a,b]

instance Invert (Edge v) where
  invert (Edge (a /\ b)) = Edge (b /\ a)

instance Ord v => Partition (Edge v) v where
  partition = pure <<< points

instance Ord v => Components (Edge v) where
  components = pure

