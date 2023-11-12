module Test.Main where

import Prelude

import Effect (Effect)
import Test.Grybu (grybuTests)

main :: Effect Unit
main = grybuTests

