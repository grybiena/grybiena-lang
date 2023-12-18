module Language.Category.Arrow where

import Prelude

import Control.Comonad.Cofree (Cofree, head, (:<))
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.App (App(..))
import Language.Category.Level (Level, toInfinity)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Inference (class Inference)
import Language.Functor.Universe (Universe, ascend)
import Language.Lambda.Unification (class Unify, unify)
import Matryoshka (class Corecursive)
import Unsafe.Coerce (unsafeCoerce)

data Arrow a = Arrow (a /\ a)


--arrow :: forall typ. Inject Level typ => Inject Arrow typ => Inject App typ => Universe typ -> Universe typ -> Universe typ
--arrow a b = In (toInfinity i) :< inj (App ((z /\ b)))
--  where
--    i = 1
--    z = In (toInfinity i :-> toInfinity i) :< (inj (App (arr /\ a)))
--    arr = In (toInfinity i :-> toInfinity i :-> toInfinity i) :< inj (Arrow i)
--
--
--
--infixr 5 arrow as :->

derive instance Generic (Arrow a) _

instance Show a => Show (Arrow a) where
  show = genericShow

instance Functor Arrow where
  map f (Arrow (a /\ b)) = Arrow (f a /\ f b)

instance
  ( Monad m 
  , Inject Arrow typ 
  , Inject Level typ
  , Inject App typ
  , Unify (Universe u typ) (Universe u typ) m
  , Corecursive (u (Cofree typ)) (Cofree typ)
  ) => Inference Arrow typ (Universe u typ) m where
    inference (Arrow (inferA /\ inferB)) = do 
       a <- inferA
       unify (toInfinity 1 :: Universe u typ) (head a)
       b <- inferB
       unify (toInfinity 1 :: Universe u typ) (head b)

       unsafeCoerce unit


 
