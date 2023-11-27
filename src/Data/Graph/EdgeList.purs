module Data.Graph.EdgeList where

import Prelude

import Data.Foldable (fold)
import Data.Graph.CC (cc)
import Data.Graph.Edge (Edge)
import Data.Graph.SCC (scc)
import Data.List (List, filter)
import Data.Relation.Invert (class Invert, invert)
import Data.Set (Set)
import Data.Topos.Intersects (intersects)
import Data.Topos.Pointed (class Pointed, points)
import Data.Topos.Pointed.Projection (class Projection, CC(..), SCC(..), projection)

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

instance Ord v => Projection CC (Graph v) (Set v) where
  projection (CC g) = map points (projection (CC g) :: List (Graph v))

instance Ord v => Projection CC (Graph v) (Graph v) where
  projection (CC (Graph es)) = Graph <$> (cc es)

instance Ord v => Projection SCC (Graph v) (Set v) where
  projection (SCC (Graph es)) = (scc es)

instance Ord v => Projection SCC (Graph v) (Graph v) where
  projection (SCC g@(Graph es)) =
    let pts :: List (Set v)
        pts = projection (SCC g)
        pick :: List (Edge v) -> Set v -> List (Edge v)
        pick l s = filter (intersects s <<< points) l
     in Graph <$> (pick es <$> pts) 
