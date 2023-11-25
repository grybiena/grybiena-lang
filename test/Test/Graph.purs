module Test.Graph where

import Prelude

import Data.List (List, fromFoldable)
import Data.Tuple.Nested ((/\))
import Data.Set as Set
import Effect (Effect)
import Language.Term.LetRec (Edge(..), Edges(..), Points(..), components, points)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

testComponents :: TestSuite
testComponents = test "components" $ do
  let e :: Array (Edge Int)
      e = Edge <$> [(1 /\ 2), (2 /\ 3), (2 /\ 6), (5 /\ 6), (6 /\ 7), (8 /\ 9), (9 /\ 10)] 
      g :: Edges Int
      g = Edges $ fromFoldable e
      cc :: List (Points Int)
      cc = points <$> components g
      expected :: List (Points Int)
      expected = (fromFoldable (Points <$> [Set.fromFoldable [8,9,10], Set.fromFoldable [1,2,3,5,6,7]]))
  Assert.equal expected cc




graphTests :: Effect Unit
graphTests = runTest do
  suite "Language.Block.Graph" do
    testComponents


