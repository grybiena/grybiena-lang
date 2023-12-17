module Language.Functor.Type.Arrow where

import Prelude

import Control.Comonad.Cofree ((:<))
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested ((/\))
import Language.Category.Inference (class Inference)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Type.App (App(..))
import Language.Functor.Type.Level (Level, toInfinity)
import Language.Functor.Type.Universe (Universe)

data Arrow :: forall k. k -> Type
data Arrow a = Arrow Int


arrow :: forall typ. Inject Level typ => Inject Arrow typ => Inject App typ => Universe typ -> Universe typ -> Universe typ
arrow a b = In (toInfinity i) :< inj (App ((z /\ b)))
  where
    i = 1
    z = In (toInfinity i :-> toInfinity i) :< (inj (App (arr /\ a)))
    arr = In (toInfinity i :-> toInfinity i :-> toInfinity i) :< inj (Arrow i)



infixr 5 arrow as :->

derive instance Generic (Arrow a) _

instance Show (Arrow a) where
  show = genericShow

instance Functor Arrow where
  map _ (Arrow i) = Arrow i

instance
  ( Monad m 
  , Inject Arrow typ 
  , Inject Level typ
  , Inject App typ
  ) => Inference Arrow typ (Universe typ) m where
    inference (Arrow i) = pure $ (toInfinity i :-> toInfinity i :-> toInfinity i) :< inj (Arrow i)


 
