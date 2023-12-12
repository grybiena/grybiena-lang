module Test.Main where

import Prelude

import Effect (Effect)
import Test.Graph (graphTests)
import Test.Term.Compile (compileTestSuite)
import Test.Term.Eval (evalTestSuite)
import Test.Term.Infer (inferTypeSuite)
import Test.Type.Infer (inferKindSuite)

main :: Effect Unit
main = do
  graphTests
  inferTypeSuite
  inferKindSuite
  compileTestSuite
  evalTestSuite
