module Test.Main where

import Prelude

import Control.Comonad.Cofree (tail)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Class.Console (logShow)
import Language.Functor.Type.Level (Level, toInfinity)
import Language.Functor.Type.Universe (Universe, ascend)
import Matryoshka (project)
import Test.Functor.Type (foofa)
import Test.Graph (graphTests)
import Test.Term.Compile (compileTestSuite)
import Test.Term.Eval (evalTestSuite)
import Test.Term.Infer (inferTypeSuite)
import Test.Type.Infer (inferKindSuite)

main :: Effect Unit
main = do
  liftEffect $ logShow $ tail $ project (toInfinity 0 :: Universe Level)
  liftEffect $ logShow $ tail $ project (ascend (toInfinity 0 :: Universe Level))
  liftEffect $ logShow $ tail $ project $ ascend (ascend (toInfinity 0 :: Universe Level))

  graphTests
  inferTypeSuite
  inferKindSuite
  compileTestSuite
  evalTestSuite

  foofa
