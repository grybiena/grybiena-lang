module Language.Kernel.Pure where

import Prelude

pureModule :: Record 
  ( intPlus :: Int -> Int -> Int
  , numPlus :: Number -> Number -> Number
  , true :: Boolean
  , false :: Boolean
  , intGt :: Int -> Int -> Boolean
  )
pureModule = 
  { "intPlus": (+)
  , "numPlus": (+)
  , "true": true
  , "false": false
  , "intGt": (>)
  }

