module Language.Functor.Elimination where

import Control.Comonad.Cofree (Cofree)
import Language.Functor.Coproduct (type (:+:), Coproduct(..))

class Elimination obj cat typ m where
  elimination :: obj (Cofree cat typ) -> typ -> m (Cofree cat typ)

instance
  ( Elimination a cat typ m
  , Elimination b cat typ m
  ) => Elimination (a :+: b) cat typ m where
    elimination (Inl a) = elimination a
    elimination (Inr b) = elimination b

