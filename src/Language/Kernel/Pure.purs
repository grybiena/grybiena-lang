module Language.Kernel.Pure where

import Prelude

import Data.Homogeneous.Record (homogeneous)
import Language.Term (Term)
import Language.Module (Module)
import Language.Type.Reify (reifyNative)
import Language.Value.Native (Native)

intPlus :: Int -> Int -> Int 
intPlus = \a b -> a + b 

numPlus :: Number -> Number -> Number
numPlus = \a b -> a + b 

type PureTermListing =
      ( intPlus :: Void                     
      , numPlus :: Void
      )

pureNatives :: forall m.
     Applicative m
  => Module
      PureTermListing
      (m (Native Term))
pureNatives = homogeneous
  { "intPlus": pure $ reifyNative intPlus
  , "numPlus": pure $ reifyNative numPlus
  }


