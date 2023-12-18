module Language.Category.Hole where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, deferCofree, (:<))
import Data.Foldable (class Foldable)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Category.Var (class Fresh, Var, fresh)
import Language.Functor.Parse (class Parse)
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

hole :: forall u t . Inject Hole t => Corecursive (u (Cofree t)) (Cofree t) => Universe u t
hole = embed (deferCofree (\_ -> (hole /\ inj Hole)))

instance
  ( Monad m
  , Fresh m
  , Inject Var typ
  ) => Elimination Hole typ f m where
    elimination Hole t = do
       v <- fresh
       pure $ t :< inj v

instance
  ( Monad m
  , Parser m
  , Alt m
  ) => Parse Hole cat f m where
  parse _ = reserved "_" *> pure Hole

