module Test.Graph where

import Prelude

import Data.Graph.Edge (Edge(..))
import Data.Graph.EdgeList as EdgeList
import Data.List (fromFoldable)
import Data.Set (Set)
import Data.Set as Set
import Data.Topos.Pointed.Projection (CC(..), SCC(..), projection)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

testComponents :: TestSuite
testComponents = test "components" $ do
  let e :: Array (Edge Int)
      e = Edge <$> [(1 /\ 2), (2 /\ 3), (2 /\ 6), (5 /\ 6), (6 /\ 7), (8 /\ 9), (9 /\ 10)] 
      g :: EdgeList.Graph Int
      g = EdgeList.Graph $ fromFoldable e
      cc :: CC (Set Int)
      cc = projection g
      expected :: CC (Set Int)
      expected = CC $ fromFoldable [Set.fromFoldable [8,9,10], Set.fromFoldable [1,2,3,5,6,7]]
  Assert.equal expected cc


testSCC :: TestSuite
testSCC = test "scc" $ do
  let e :: Array (Edge Int)
      e = Edge <$> [(1 /\ 2), (2 /\ 3), (3 /\ 1), (5 /\ 6), (6 /\ 7), (7 /\ 5),(2 /\ 7)] 
      g :: EdgeList.Graph Int
      g = EdgeList.Graph $ fromFoldable e
      cc :: SCC (Set Int)
      cc = projection g
      expected :: SCC (Set Int)
      expected = SCC $ fromFoldable [Set.fromFoldable [1,2,3], Set.fromFoldable [5,6,7]]

  Assert.equal expected cc


testSCCBroken :: TestSuite
testSCCBroken = test "sccBroken" $ do
  let e :: Array (Edge Int)
      e = Edge <$> [(1 /\ 2), (2 /\ 3), (3 /\ 1), (5 /\ 6), (6 /\ 7), (7 /\ 5),(7 /\ 2)] 
      g :: EdgeList.Graph Int
      g = EdgeList.Graph $ fromFoldable e
      cc :: SCC (Set Int)
      cc = projection g
      expected :: SCC (Set Int)
      expected = SCC $ fromFoldable [Set.fromFoldable [5,6,7],Set.fromFoldable [1,2,3]]

  Assert.equal expected cc



graphTests :: Effect Unit
graphTests = runTest do
  suite "Language.Block.Graph" do
    testComponents
    testSCC
    testSCCBroken

