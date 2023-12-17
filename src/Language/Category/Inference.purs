module Language.Category.Inference where

import Prelude

import Control.Comonad.Cofree (Cofree)
import Language.Functor.Coproduct (type (:+:), Coproduct(..))

class (Functor obj, Functor cat) <= Inference obj cat typ m where
  inference :: obj (m (Cofree cat typ)) -> m (Cofree cat typ)


instance
  ( Inference a cat typ m
  , Inference b cat typ m
  ) => Inference (a :+: b) cat typ m where
    inference (Inl a) = inference a
    inference (Inr b) = inference b


