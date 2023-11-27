module Data.Graph.EdgeList where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Foldable (fold)
import Data.Graph.Edge (Edge)
import Data.List (List(..), (:))
import Data.List as List
import Data.Relation.Invert (class Invert, invert)
import Data.Topos.Components (class Components, components)
import Data.Topos.Intersects (intersects)
import Data.Topos.Pointed (class Pointed, points)
import Data.Topos.Pointed.Partition (class Partition)
import Data.Tuple.Nested (type (/\), (/\))

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

instance Ord v => Partition (Graph v) v where
  partition = map points <<< components

instance Ord v => Components (Graph v) where
  components e = tailRec findComponents (Nil /\ e) 
    where
      findComponents :: (List (Graph v) /\ Graph v) -> Step (List (Graph v) /\ Graph v) (List (Graph v))
      findComponents (d /\ t) =
        case saturateFirst t of
          (f /\ Graph Nil) -> Done (f:d)
          (f /\ g) -> Loop ((f:d) /\ g)
  
        where
          saturateFirst :: Graph v -> (Graph v/\ Graph v)
          saturateFirst = tailRec saturate <<< groupFirst 
            where
              saturate :: (Graph v/\ Graph v) -> Step (Graph v /\ Graph v) (Graph v /\ Graph v)
              saturate x@(_ /\ Graph Nil) = Done x
              saturate (f /\ Graph r) =
                let { yes, no } = List.partition (intersects f) r
                  in if r == no
                       then Done ((f <> Graph yes) /\ Graph no)
                       else Loop ((f <> Graph yes) /\ Graph no)
           
              groupFirst :: Graph v -> (Graph v /\ Graph v)
              groupFirst (Graph Nil) = Graph Nil /\ Graph Nil 
              groupFirst (Graph (a:r)) =
                let { yes, no } = List.partition (intersects a) r
                  in Graph (a:yes) /\ Graph no
 


