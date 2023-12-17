module Test.Main where

import Prelude

import Control.Comonad.Cofree (tail)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Class.Console (logShow)
import Language.Functor.Type.Level (Level, toInfinity)
import Language.Functor.Type.Universe (Universe, ascend)
import Test.Graph (graphTests)
import Test.Term.Compile (compileTestSuite)
import Test.Term.Eval (evalTestSuite)
import Test.Term.Infer (inferTypeSuite)
import Test.Type.Infer (inferKindSuite)

main :: Effect Unit
main = do
  liftEffect $ logShow $ tail (toInfinity 0 :: Universe Level)
  liftEffect $ logShow $ tail (ascend (toInfinity 0 :: Universe Level))
  liftEffect $ logShow $ tail $ ascend (ascend (toInfinity 0 :: Universe Level))

  graphTests
  inferTypeSuite
  inferKindSuite
  compileTestSuite
  evalTestSuite
