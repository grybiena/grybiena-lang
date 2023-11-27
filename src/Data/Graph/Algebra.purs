module Data.Graph.Algebra where

import Data.Functor.Mu (Mu(..))
import Data.Topos.Graph as Topos

data GraphF v a = 
    Empty
  | Vertex v
  | Overlay a a
  | Connect a a

type Graph v = Mu (GraphF v)

instance Topos.Graph (GraphF v (Graph v)) v where
  empty = Empty
  vertex = Vertex
  overlay a b = Overlay (In a) (In b)
  connect a b = Connect (In a) (In b)


