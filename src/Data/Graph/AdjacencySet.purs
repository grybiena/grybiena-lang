module Data.Graph.AdjacencySet where

import Prelude

import Data.Foldable (elem, fold, foldr)
import Data.Graph.Edge (Edge(..))
import Data.Graph.EdgeList (class EdgeList, edgeList)
import Data.Graph.EdgeList as EdgeList
import Data.List (List, fromFoldable)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (maybe)
import Data.Relation.Invert (class Invert, invert)
import Data.Set (Set)
import Data.Set as Set
import Data.Topos.Pointed (class Pointed)
import Data.Topos.Pointed.Partition (class Partition, CC(..), partition)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))


newtype Graph v = Graph (Map v (Set v))
derive newtype instance Eq v => Eq (Graph v)
derive newtype instance Show v => Show (Graph v)

class AdjacencySet g v | g -> v where
  adjacencySet :: g -> Graph v

instance EdgeList (Graph v) v where 
  edgeList (Graph g) =
    let squash :: List (v /\ List v)
        squash = map Set.toUnfoldable <$> Map.toUnfoldable g
        pair :: (v /\ List v) -> List (Edge v)
        pair (v /\ rs) = Edge <<< Tuple v <$> rs
     in EdgeList.Graph (join (pair <$> squash))

instance Ord v => Pointed (Graph v) v where
  points (Graph g) = Map.keys g <> fold (Map.values g)

instance Ord v => Invert (Graph v) where
  invert g@(Graph m) =
    let addEdge :: Edge v -> Map v (Set v) -> Map v (Set v) 
        addEdge (Edge (a /\ b)) o = Map.insert a (maybe (Set.singleton b) (Set.insert b) (Map.lookup a o)) o
        EdgeList.Graph i = invert $ edgeList g
     in Graph (foldr addEdge ((const Set.empty) <$> m) i)

instance Ord v => Partition CC (Graph v) (Set v) where
  partition (CC g@(Graph m)) =
    let connected = partition (CC (edgeList g))
        singletons :: Set v
        singletons = Map.keys m `Set.difference` fold connected
        singletonPoints :: List (Set v)
        singletonPoints = Set.singleton <$> fromFoldable singletons
     in (singletonPoints <> connected) 

instance Ord v => Partition CC (Graph v) (Graph v) where
  partition (CC g@(Graph m)) =
    let subgraph :: Set v -> Graph v
        subgraph p = Graph $ Map.filterKeys (\k -> k `elem` p) m
        cc = partition (CC g)
     in subgraph <$> cc 


