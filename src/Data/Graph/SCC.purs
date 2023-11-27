module Data.Graph.SCC (scc) where

-- based on a Haskell implementation of Tarjan's SCC algorithm by @paf31
-- https://github.com/purescript-deprecated/purescript-maps/commit/c976f02e53dd22bf12418a034eea0e971bb09cb5

-- refactored to be clearly isomorphic to Tarjan's algorithm as described here
-- https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm 

import Prelude

import Control.Monad.RWS (RWS, execRWS)
import Control.Monad.Reader (class MonadReader, ask)
import Control.Monad.State (class MonadState, modify_)
import Control.Monad.State.Class (gets)
import Data.Foldable (elem)
import Data.Graph.Edge (Edge(..))
import Data.List (List(..), filter, fold, (:))
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Topos.Pointed (points)
import Data.Traversable (sequence_, traverse_)
import Data.Tuple (fst)
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
  let f :: RWS (List (Edge v)) Unit (SCCState v) Unit
      f = (sequence_ $ map strongConnect (List.fromFoldable $ fold (points <$> g)))
      st = fst $ execRWS f g initialSCCState
  in st.components
 
strongConnect :: forall v m.
          MonadState (SCCState v) m
       => MonadReader (List (Edge v)) m
       => Ord v => v -> m Unit 
strongConnect v = do
  whenIndexUndefined v do
    initVertex v
    onSuccessors v $ \w -> do
      notVisited <- isNothing <$> indexOf w
      if notVisited 
        then do
          strongConnect w
          updateLowLink v w
        else do
          whenOnStack w do
            altUpdateLowLink v w
    whenIsRootNode v do
      generateSCC v

initialSCCState :: forall v. SCCState v
initialSCCState =
  { index            : 0
  , path             : mempty
  , indexMap         : Map.empty
  , lowlinkMap       : Map.empty 
  , components       : mempty
  }

initVertex :: forall v m. MonadState (SCCState v) m => Ord v => v -> m Unit
initVertex v = modify_ $ \st ->
  st { indexMap = Map.insert v st.index st.indexMap
     , lowlinkMap = Map.insert v st.index st.lowlinkMap
     , index = st.index + 1
     , path = v:st.path
     }

indexOf :: forall v m. MonadState (SCCState v) m => Ord v => v -> m (Maybe Index)
indexOf v = gets (\st -> Map.lookup v st.indexMap)

lowLinkOf :: forall v m. MonadState (SCCState v) m => Ord v => v -> m (Maybe Index)
lowLinkOf v = gets (\st -> Map.lookup v st.lowlinkMap)

onSuccessors :: forall v m.
                 MonadState (SCCState v) m
              => MonadReader (List (Edge v)) m
              => Ord v => v -> (v -> m Unit) -> m Unit 
onSuccessors v f = do
  es <- ask
  let isSuccessor (Edge (v' /\ _)) = v' == v
      successor (Edge (_ /\ w)) = w
  traverse_ f (successor <$> (filter isSuccessor es)) 

whenIndexUndefined :: forall v m. MonadState (SCCState v) m => Ord v => v -> m Unit -> m Unit 
whenIndexUndefined v f = do
  i <- indexOf v
  case i of
    Nothing -> f
    _ -> pure unit

updateLowLink :: forall v m. MonadState (SCCState v) m => Ord v => v -> v -> m Unit
updateLowLink v w = do
  vll <- lowLinkOf v
  wll <- lowLinkOf w
  flip traverse_ (min <$> vll <*> wll) $ \n -> do
    modify_ (\st -> st { lowlinkMap = Map.insert v n st.lowlinkMap })

altUpdateLowLink :: forall v m. MonadState (SCCState v) m => Ord v => v -> v -> m Unit
altUpdateLowLink v w = do
  vll <- lowLinkOf v
  wll <- indexOf w
  flip traverse_ (min <$> vll <*> wll) $ \n -> do
    modify_ (\st -> st { lowlinkMap = Map.insert v n st.lowlinkMap })

whenOnStack :: forall v m. MonadState (SCCState v) m => Ord v => v -> m Unit -> m Unit 
whenOnStack v f = do
  on <- gets (\st -> v `elem` st.path)
  when on f

whenIsRootNode :: forall v m. MonadState (SCCState v) m => Ord v => v -> m Unit -> m Unit 
whenIsRootNode v f = do 
  vll <- lowLinkOf v
  vin <- indexOf v
  when (vll == vin) f

generateSCC :: forall v m. MonadState (SCCState v) m => Ord v => v -> m Unit
generateSCC v = do
  modify_ (\st -> let newPath = popUntil v st.path Nil
                   in st { components = newPath.component : st.components
                         , path = newPath.path
                         })

popUntil :: forall v. Eq v => v -> List v -> List v -> { path :: List v, component :: List v }
popUntil _ Nil popped = { path: Nil, component: popped } 
popUntil v (w : path) popped | v == w = { path: path, component: w : popped }
popUntil v (w : ws) popped = popUntil v ws (w : popped)

