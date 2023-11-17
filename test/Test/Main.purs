module Test.Main where

import Prelude

import Effect (Effect)
import Test.Term (termTests)

main :: Effect Unit
main = termTests

