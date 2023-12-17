module Language.Functor.Type.App where

import Data.Tuple.Nested (type (/\))

newtype App a = App (a /\ a)


