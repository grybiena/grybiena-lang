module Data.Graph.SCC (scc) where

-- based on a Haskell implementation of Tarjan's SCC algorithm by @paf31
-- https://github.com/purescript-deprecated/purescript-maps/commit/c976f02e53dd22bf12418a034eea0e971bb09cb5

import Prelude

import Data.Foldable (elem, foldl)
import Data.Graph.Edge (Edge(..))
import Data.List (List(..), fold, (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Topos.Pointed (points)
import Data.Tuple.Nested ((/\))

type Index = Int

type SCCState v =
  { index            :: Index
  , path             :: List v 
  , indexMap         :: Map v Index
  , lowlinkMap       :: Map v Index
  , components       :: List (List v)
  }

scc :: forall v. Ord v => List (Edge v) -> List (Set v)
scc g = 
  let st = foldl (scc' g) initialSCCState (fold (points <$> g))
  in Set.fromFoldable <$> st.components

initialSCCState :: forall v. SCCState v
initialSCCState =
  { index            : 0
  , path             : mempty
  , indexMap         : Map.empty
  , lowlinkMap       : Map.empty 
  , components       : mempty
  }

scc' :: forall v. Ord v => List (Edge v) -> SCCState v -> v -> SCCState v
scc' es sccst iv | Map.lookup iv sccst.indexMap == Nothing = 
  let indexOf   st' v' = Map.lookup v' st'.indexMap
      lowlinkOf st' v' = Map.lookup v' st'.lowlinkMap

      st1 = sccst { indexMap         = Map.insert iv sccst.index sccst.indexMap
               , lowlinkMap       = Map.insert iv sccst.index sccst.lowlinkMap
               , index            = sccst.index + 1 
               , path             = iv : sccst.path
               }

      st2 = foldl (\st (Edge (v /\ w)) ->
             case indexOf st w of
               Nothing -> let st' = scc' es st w in
                          case min <$> lowlinkOf st' v <*> lowlinkOf st' w of
                            Just min -> st' { lowlinkMap = Map.insert v min st'.lowlinkMap }
                            _ -> st'
               _ -> case w `elem` st.path of
                 true -> case min <$> lowlinkOf st v <*> indexOf st w of
                   Just min -> st { lowlinkMap = Map.insert v min st.lowlinkMap }
                   _ -> st
                 false -> st) st1 es
   in if st2 `indexOf` iv == st2 `lowlinkOf` iv
        then let newPath = popUntil iv st2.path Nil
               in st2 { components = newPath.component : st2.components
                      , path = newPath.path
                      }
        else st2 
scc' _ st _ = st

popUntil :: forall v. Eq v => v -> List v -> List v -> { path :: List v, component :: List v }
popUntil _ Nil popped = { path: Nil, component: popped } 
popUntil v (w : path) popped | v == w = { path: path, component: w : popped }
popUntil v (w : ws) popped = popUntil v ws (w : popped)

