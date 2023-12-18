module Language.Functor.Application where

import Data.Tuple.Nested (type (/\))

class Application obj where
  app :: forall a. a -> a -> obj a
  unApp :: forall a. obj a -> (a /\ a)
