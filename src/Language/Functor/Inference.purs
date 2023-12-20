module Language.Functor.Inference where

import Control.Comonad.Cofree (Cofree)
import Language.Functor.Coproduct (type (:+:), Coproduct(..))
import Type.Proxy (Proxy)

class Inference :: forall k. k -> (Type -> Type) -> (Type -> Type) -> Type -> (Type -> Type) -> Constraint
class Inference var obj cat typ m where
  inference :: Proxy var -> obj (m (Cofree cat typ)) -> m (Cofree cat typ)



instance
  ( Inference var a cat typ m
  , Inference var b cat typ m
  ) => Inference var (a :+: b) cat typ m where
    inference p (Inl a) = inference p a
    inference p (Inr b) = inference p b

