module Test.Main where

import Prelude

import Effect (Effect)
import Test.Graph (graphTests)
import Test.Term (termTests)

main :: Effect Unit
main = do
  termTests
  graphTests

