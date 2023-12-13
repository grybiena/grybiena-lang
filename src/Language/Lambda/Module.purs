module Language.Lambda.Module where


import Prelude

import Data.Either (Either(..))
import Data.Foldable (class Foldable)
import Data.Graph.AdjacencySet (class AdjacencySet, Graph(..), adjacencySet)
import Data.List (List, elem)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Topos.Pointed.Projection (class Projection, CC, SCC(..), projection)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (class FreeVars, LambdaF, free, freeIn)
import Matryoshka (class Recursive)

newtype Module var term = Module (Map var term)
derive newtype instance (Show var, Show term) => Show (Module var term)
derive newtype instance (Eq var, Eq term) => Eq (Module var term)
derive newtype instance (Ord var, Ord term) => Ord (Module var term)
derive newtype instance Functor (Module var)
derive newtype instance Foldable (Module var)
derive newtype instance Traversable (Module var)

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
  , FreeVars abs var cat
  ) => AdjacencySet (Module var (f (LambdaF abs var cat))) var where
  adjacencySet (Module b) = Graph ((Set.filter (flip elem (Map.keys b)) <<< Set.fromFoldable <<< free) <$> b)

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
  , FreeVars abs var cat
  ) => Projection CC (Module var (f (LambdaF abs var cat))) (Module var (f (LambdaF abs var cat))) where
  projection g@(Module m) =
    let subblock :: Set var -> Module var (f (LambdaF abs var cat))
        subblock p = Module $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (projection (adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
  , FreeVars abs var cat
  ) => Projection CC (Module var (f (LambdaF abs var cat))) (Set var) where
  projection = projection <<< adjacencySet

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
  , FreeVars abs var cat
  ) => Projection SCC (Module var (f (LambdaF abs var cat))) (Module var (f (LambdaF abs var cat))) where
  projection g@(Module m) =
    let subblock :: Set var -> Module var (f (LambdaF abs var cat))
        subblock p = Module $ Map.filterKeys (\k -> k `elem` p) m
     in subblock <$> (projection (adjacencySet g))

instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
  , FreeVars abs var cat
  ) => Projection SCC (Module var (f (LambdaF abs var cat))) (Set var) where
  projection = projection <<< adjacencySet

type Binding var term = var /\ term
type Bindings var term = List (Binding var term)

sequenceBindings :: forall f abs var cat.
          Ord var
       => Foldable cat
       => Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
       => Eq (f (LambdaF abs var cat))
       => FreeVars abs var cat
       => Module var (f (LambdaF abs var cat))
       -> Either (Module var (f (LambdaF abs var cat))) (Bindings var (f (LambdaF abs var cat)))
sequenceBindings lr =
      let SCC (scc :: List (Module var (f (LambdaF abs var cat)))) = projection lr
          failOnSCC :: Module var (f (LambdaF abs var cat))
                    -> Either (Module var (f (LambdaF abs var cat))) (Binding var (f (LambdaF abs var cat))) 
          failOnSCC (Module s) = case Map.toUnfoldable s of
                  [v /\ t] -> if v `freeIn` t then Left (Module s) else Right (v /\ t)
                  _ -> Left $ Module s
       in traverse failOnSCC scc

sequenceBindings' :: forall f abs var cat.
          Ord var
       => Foldable cat
       => Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
       => Eq (f (LambdaF abs var cat))
       => FreeVars abs var cat
       => Module var (f (LambdaF abs var cat))
       -> Either (Module var (f (LambdaF abs var cat))) (Bindings var (f (LambdaF abs var cat)))
sequenceBindings' lr =
      let SCC (scc :: List (Module var (f (LambdaF abs var cat)))) = projection lr
          failOnSCC :: Module var (f (LambdaF abs var cat))
                    -> Either (Module var (f (LambdaF abs var cat))) (Binding var (f (LambdaF abs var cat))) 
          failOnSCC (Module s) = case Map.toUnfoldable s of
                  [v /\ t] -> if v `freeIn` t then Left (Module s) else Right (v /\ t)
                  _ -> Left $ Module s
       in traverse failOnSCC scc

