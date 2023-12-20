module Language.Category.Hole where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, deferCofree, (:<))
import Control.Plus (class Plus, empty)
import Data.Foldable (class Foldable)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Unification (class Unification)
import Language.Functor.Universe (Universe)
import Language.Monad.Parser (class Parser, reserved)
import Matryoshka (class Corecursive, embed)

data Hole :: forall k. k -> Type
data Hole a = Hole

instance Show (Hole a) where
  show Hole = "_"

instance Functor Hole where
  map _ Hole = Hole

instance Foldable Hole where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

instance Traversable Hole where
  traverse _ _ = pure Hole
  sequence = traverse identity


instance 
  ( Monad m
  , Inject Hole t
  , Corecursive (u (Cofree t)) (Cofree t)
  ) => Inference Hole t (Universe u t) m where
    inference Hole = pure $ hole :< inj Hole 

instance
  ( Monad m
  ) => Unification Hole Hole t i m where
    unification _ _ = pure Nil 
else
instance
  ( Monad m
  ) => Unification Hole a t i m where
    unification _ _ = pure Nil 
else
instance
  ( Monad m
  ) => Unification a Hole t i m where
    unification _ _ = pure Nil




hole :: forall u t . Inject Hole t => Corecursive (u (Cofree t)) (Cofree t) => Universe u t
hole = embed (deferCofree (\_ -> (hole /\ inj Hole)))

instance
  ( Monad m
  ) => Elimination Hole typ f m where
    elimination Hole _ = pure Nothing

 

instance
  ( Plus p
  ) => Postfix p Hole cat f m where
  postfix = pure empty


instance
  ( Monad m
  , Parser m
  , Alt m
  ) => Parse Hole cat f m where
  parse _ = pure $ reserved "_" *> pure Hole

