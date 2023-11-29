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
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested (type (/\))
import Language.Lambda.Calculus (LambdaF, free)
import Matryoshka (class Recursive)

newtype Block var term = Block (Map var term)
derive newtype instance (Show var, Show term) => Show (Block var term)
derive newtype instance (Eq var, Eq term) => Eq (Block var term)
derive newtype instance (Ord var, Ord term) => Ord (Block var term)
derive newtype instance Functor (Block var)
derive newtype instance Foldable (Block var)
derive newtype instance Traversable (Block var)

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => AdjacencySet (Block var (f (LambdaF var cat))) var where
  adjacencySet (Block b) = Graph ((Set.filter (flip elem (Map.keys b)) <<< free) <$> b)

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection CC (Block var (f (LambdaF var cat))) (Block var (f (LambdaF var cat))) where
  projection g@(Block m) =
    let subblock :: Set var -> Block var (f (LambdaF var cat))
        subblock p = Block $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (projection (adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection CC (Block var (f (LambdaF var cat))) (Set var) where
  projection = projection <<< adjacencySet

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection SCC (Block var (f (LambdaF var cat))) (Block var (f (LambdaF var cat))) where
  projection g@(Block m) =
    let subblock :: Set var -> Block var (f (LambdaF var cat))
        subblock p = Block $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (projection (adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Projection SCC (Block var (f (LambdaF var cat))) (Set var) where
  projection = projection <<< adjacencySet

type Binding var term = var /\ term
type Bindings var term = List (Binding var term)

sequenceBindings :: forall f var cat.
          Ord var
       => Foldable cat
       => Recursive (f (LambdaF var cat)) (LambdaF var cat)
       => Eq (f (LambdaF var cat))
       => Block var (f (LambdaF var cat))
       -> Either (Block var (f (LambdaF var cat))) (Bindings var (f (LambdaF var cat)))
sequenceBindings lr =
      let SCC (scc :: List (Block var (f (LambdaF var cat)))) = projection lr
          failOnSCC :: Block var (f (LambdaF var cat))
                    -> Either (Block var (f (LambdaF var cat))) (Binding var (f (LambdaF var cat))) 
          failOnSCC (Block s) = case Map.toUnfoldable s of
                  [z] -> Right z
                  _ -> Left $ Block s
       in reverse <$> traverse failOnSCC scc

