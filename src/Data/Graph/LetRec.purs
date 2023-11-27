module Data.Graph.LetRec where


import Prelude

import Data.Foldable (class Foldable)
import Data.Graph.AdjacencySet (class AdjacencySet, Graph(..), adjacencySet)
import Data.List (elem)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Topos.Components (class Components, components)
import Data.Topos.Pointed (points)
import Data.Topos.Pointed.Partition (class Partition, partition)
import Language.Lambda.Calculus (LambdaF, free)
import Matryoshka (class Recursive)

newtype LetRec f var cat = LetRec (Map var (f (LambdaF var cat)))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => AdjacencySet (LetRec f var cat) var where
  adjacencySet (LetRec b) = Graph ((Set.filter (flip elem (Map.keys b)) <<< free) <$> b)

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Components (LetRec f var cat) where
  components g@(LetRec m) =
    let subblock :: Set var -> LetRec f var cat
        subblock p = LetRec $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (points <$> (components $ adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Partition (LetRec f var cat) var where
  partition = partition <<< adjacencySet

