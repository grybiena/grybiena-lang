module Language.Kernel.Library.Pure where

import Prelude

import Data.Homogeneous.Record (homogeneous)
import Language.Grybu (Term)
import Language.Kernel.Library (KernelLibrary)
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

pureNatives :: forall m n.
     Applicative m
  => KernelLibrary
      PureTermListing
      (m (Native (Term n)))
pureNatives = homogeneous
  { "intPlus": pure $ reifyNative intPlus
  , "numPlus": pure $ reifyNative numPlus
  }


