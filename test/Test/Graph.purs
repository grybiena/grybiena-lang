module Test.Graph where

import Prelude

import Data.Graph.Edge (Edge(..))
import Data.Graph.EdgeList as EdgeList
import Data.List (List, fromFoldable)
import Data.Set (Set)
import Data.Set as Set
import Data.Topos.Pointed.Partition (CC(..), partition)
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
      cc :: List (Set Int)
      cc = partition (CC g)
      expected :: List (Set Int)
      expected = fromFoldable [Set.fromFoldable [8,9,10], Set.fromFoldable [1,2,3,5,6,7]]
  Assert.equal expected cc




graphTests :: Effect Unit
graphTests = runTest do
  suite "Language.Block.Graph" do
    testComponents


