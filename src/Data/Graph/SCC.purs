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

scc :: forall v. Ord v => List (Edge v) -> List (List v)
scc g = 
  let st = foldl (scc' g) initialSCCState (fold (points <$> g))
  in st.components

initialSCCState :: forall v. SCCState v
initialSCCState =
  { index            : 0
  , path             : mempty
  , indexMap         : Map.empty
  , lowlinkMap       : Map.empty 
  , components       : mempty
  }


initVertex :: forall v. Ord v => SCCState v -> v -> SCCState v
initVertex st v =
  st { indexMap = Map.insert v st.index st.indexMap
     , lowlinkMap = Map.insert v st.index st.lowlinkMap
     , index = st.index + 1
     , path = v:st.path
     }

onSuccessors :: forall v. Ord v => List (Edge v) -> SCCState v -> v -> (SCCState v -> v -> SCCState v) -> SCCState v
onSuccessors es st v f = foldl (\st' (Edge (v' /\ w)) -> if v == v' then f st' w else st') st es


scc' :: forall v. Ord v => List (Edge v) -> SCCState v -> v -> SCCState v
scc' es sccst v | Map.lookup v sccst.indexMap == Nothing = 
  let indexOf   st' v' = Map.lookup v' st'.indexMap
      lowlinkOf st' v' = Map.lookup v' st'.lowlinkMap

      st1 = initVertex sccst v 

      st2 = onSuccessors es st1 v (\st w ->
              case indexOf st w of
                Nothing ->
                  let st' = scc' es st w
                   in case min <$> lowlinkOf st' v <*> lowlinkOf st' w of
                        Just min -> st' { lowlinkMap = Map.insert v min st'.lowlinkMap }
                        _ -> st'
                _ ->
                  if w `elem` st.path
                    then case min <$> lowlinkOf st v <*> indexOf st w of
                           Just min -> st { lowlinkMap = Map.insert v min st.lowlinkMap }
                           _ -> st
                    else st
                )
   in if st2 `indexOf` v == st2 `lowlinkOf` v
        then let newPath = popUntil v st2.path Nil
               in st2 { components = newPath.component : st2.components
                      , path = newPath.path
                      }
        else st2 
scc' _ st _ = st

popUntil :: forall v. Eq v => v -> List v -> List v -> { path :: List v, component :: List v }
popUntil _ Nil popped = { path: Nil, component: popped } 
popUntil v (w : path) popped | v == w = { path: path, component: w : popped }
popUntil v (w : ws) popped = popUntil v ws (w : popped)

