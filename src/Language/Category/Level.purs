module Language.Category.Level where

import Prelude

import Control.Alt (class Alt)
import Control.Alternative (class Plus)
import Control.Comonad.Cofree (Cofree, deferCofree, (:<))
import Control.Plus (empty)
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Unification (class Unification)
import Language.Functor.Universe (Universe)
import Language.Monad.Parser (class Parser, reservedOp)
import Matryoshka (class Corecursive, embed)

newtype Level :: forall k. k -> Type
newtype Level a = Level Int

derive instance Generic (Level a) _

instance Show (Level a) where
  show = genericShow

instance Functor Level where
  map _ (Level i) = Level i

instance Foldable Level where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

instance Traversable Level where
  traverse _ (Level v) = pure (Level v)
  sequence = traverse identity

instance
  ( Plus p
  ) => Postfix p Level cat f m where
  postfix = pure empty


instance
  ( Monad m
  , Parser m
  , Alt m
  ) => Parse Level cat f m where
  parse _ = pure do
      reservedOp "*"
      pure $ Level 1

instance
  ( Monad m 
  , Inject Level t 
  , Corecursive (u (Cofree t)) (Cofree t)
  ) => Inference Level t (Universe u t) m where
    inference (Level i) = pure $ (toInfinity (i+1)) :< inj (Level i) 

toInfinity :: forall u t. Inject Level t => Corecursive (u (Cofree t)) (Cofree t) => Int -> Universe u t 
toInfinity i = embed (deferCofree (\_ -> (toInfinity (i+1) /\ inj (Level i))))


instance
  ( Monad m
  ) => Unification Level Level i m where
    unification (Level i) t = pure Nil 
else 
instance
  ( Monad m
  ) => Unification a Level i m where
    unification _ _ = pure Nil
else 
instance
  ( Monad m
  ) => Unification Level a i m where
    unification _ _ = pure Nil


instance (Applicative m) => Elimination Level cat t m where
  elimination _ _ = pure Nothing


 
