module Language.Kernel.Pure where

import Prelude

pureModule :: Record 
  ( intPlus :: Int -> Int -> Int
  , numPlus :: Number -> Number -> Number
  )
pureModule = 
  { "intPlus": (+)
  , "numPlus": (+)
  }

