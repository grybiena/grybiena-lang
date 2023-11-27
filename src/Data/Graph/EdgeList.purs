module Data.Graph.EdgeList where

import Prelude

import Data.Foldable (fold)
import Data.Graph.CC (cc)
import Data.Graph.Edge (Edge)
import Data.Graph.SCC (scc)
import Data.List (List)
import Data.Relation.Invert (class Invert, invert)
import Data.Set (Set)
import Data.Topos.Pointed (class Pointed, points)
import Data.Topos.Pointed.Partition (class Partition, CC(..), SCC(..), partition)

newtype Graph v = Graph (List (Edge v))
derive newtype instance Eq v => Eq (Graph v)
derive newtype instance Show v => Show (Graph v)
derive newtype instance Semigroup (Graph v)
derive newtype instance Monoid (Graph v)

class EdgeList g v | g -> v where
  edgeList :: g -> Graph v

instance Ord v => Pointed (Graph v) v where
  points (Graph e) = fold (points <$> e)

instance Invert (Graph v) where
  invert (Graph es) = Graph (invert <$> es)

instance Ord v => Partition CC (Graph v) (Set v) where
  partition (CC g) = map points (partition (CC g) :: List (Graph v))

instance Ord v => Partition CC (Graph v) (Graph v) where
  partition (CC (Graph es)) = Graph <$> (cc es)

instance Ord v => Partition SCC (Graph v) (Set v) where
  partition (SCC (Graph es)) = (scc es)


