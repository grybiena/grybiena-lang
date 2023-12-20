module Language.Functor.Inference where

import Control.Comonad.Cofree (Cofree)
import Language.Functor.Coproduct (type (:+:), Coproduct(..))

class Inference obj cat typ m where
  inference :: obj (m (Cofree cat typ)) -> m (Cofree cat typ)



instance
  ( Inference a cat typ m
  , Inference b cat typ m
  ) => Inference (a :+: b) cat typ m where
    inference (Inl a) = inference a
    inference (Inr b) = inference b

