module Data.Topos.Graph where

class Graph g v | g -> v where
  empty :: g
  vertex :: v -> g
  overlay :: g -> g -> g
  connect :: g -> g -> g
  
