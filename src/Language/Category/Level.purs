module Language.Category.Level where

import Prelude

import Control.Comonad.Cofree (Cofree, deferCofree, (:<))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested ((/\))
import Language.Functor.Inference (class Inference)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Universe (Universe)
import Matryoshka (class Corecursive, embed)

newtype Level :: forall k. k -> Type
newtype Level a = Level Int

derive instance Generic (Level a) _

instance Show (Level a) where
  show = genericShow

instance Functor Level where
  map _ (Level i) = Level i

instance
  ( Monad m 
  , Inject Level t 
  , Corecursive (u (Cofree t)) (Cofree t)
  ) => Inference Level t (Universe u t) m where
    inference (Level i) = pure $ (toInfinity (i+1)) :< inj (Level i) 

toInfinity :: forall u t. Inject Level t => Corecursive (u (Cofree t)) (Cofree t) => Int -> Universe u t 
toInfinity i = embed (deferCofree (\_ -> (toInfinity (i+1) /\ inj (Level i))))

 
