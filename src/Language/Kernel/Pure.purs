module Language.Kernel.Pure where

import Prelude

pureModule :: Record 
  ( intPlus :: Int -> Int -> Int
  , numPlus :: Number -> Number -> Number
  , true :: Boolean
  , false :: Boolean
  )
pureModule = 
  { "intPlus": (+)
  , "numPlus": (+)
  , "true": true
  , "false": false
  }

