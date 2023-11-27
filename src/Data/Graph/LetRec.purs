module Data.Graph.LetRec where


import Prelude

import Data.Foldable (class Foldable)
import Data.Graph.AdjacencySet (class AdjacencySet, Graph(..), adjacencySet)
import Data.List (elem)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Topos.Pointed.Projection (class Projection, CC, SCC, projection)
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
  ) => Projection CC (LetRec f var cat) (LetRec f var cat) where
  projection g@(LetRec m) =
    let subblock :: Set var -> LetRec f var cat
        subblock p = LetRec $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (projection (adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection CC (LetRec f var cat) (Set var) where
  projection = projection <<< adjacencySet

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection SCC (LetRec f var cat) (LetRec f var cat) where
  projection g@(LetRec m) =
    let subblock :: Set var -> LetRec f var cat
        subblock p = LetRec $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (projection (adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection SCC (LetRec f var cat) (Set var) where
  projection = projection <<< adjacencySet

