module Language.Lambda.Block where


import Prelude

import Data.Either (Either(..))
import Data.Foldable (class Foldable)
import Data.Graph.AdjacencySet (class AdjacencySet, Graph(..), adjacencySet)
import Data.List (List, elem, reverse)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Topos.Pointed.Projection (class Projection, CC, SCC(..), projection)
import Data.Traversable (traverse)
import Data.Tuple.Nested (type (/\))
import Language.Lambda.Calculus (LambdaF, free)
import Matryoshka (class Recursive)

newtype Block f var cat = Block (Map var (f (LambdaF var cat)))
derive newtype instance (Show var, Show (f (LambdaF var cat))) => Show (Block f var cat)
derive newtype instance (Eq var, Eq (f (LambdaF var cat))) => Eq (Block f var cat)
derive newtype instance (Ord var, Ord (f (LambdaF var cat))) => Ord (Block f var cat)


instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => AdjacencySet (Block f var cat) var where
  adjacencySet (Block b) = Graph ((Set.filter (flip elem (Map.keys b)) <<< free) <$> b)

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection CC (Block f var cat) (Block f var cat) where
  projection g@(Block m) =
    let subblock :: Set var -> Block f var cat
        subblock p = Block $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (projection (adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection CC (Block f var cat) (Set var) where
  projection = projection <<< adjacencySet

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection SCC (Block f var cat) (Block f var cat) where
  projection g@(Block m) =
    let subblock :: Set var -> Block f var cat
        subblock p = Block $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (projection (adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection SCC (Block f var cat) (Set var) where
  projection = projection <<< adjacencySet

type Binding f var cat = var /\ f (LambdaF var cat)
type Bindings f var cat = List (Binding f var cat)

sequenceBindings :: forall f var cat.
          Ord var
       => Foldable cat
       => Recursive (f (LambdaF var cat)) (LambdaF var cat)
       => Eq (f (LambdaF var cat))
       => Block f var cat ->  Either (Block f var cat) (Bindings f var cat)
sequenceBindings lr =
      let SCC (scc :: List (Block f var cat)) = projection lr
          failOnSCC :: Block f var cat -> Either (Block f var cat) (Binding f var cat) 
          failOnSCC (Block s) = case Map.toUnfoldable s of
                  [z] -> Right z
                  _ -> Left $ Block s
       in reverse <$> traverse failOnSCC scc

