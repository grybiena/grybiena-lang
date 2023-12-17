module Language.Functor.Ident.Hole where

import Prelude

import Control.Comonad.Cofree (deferCofree, (:<))
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Language.Category.Elimination (class Elimination)
import Language.Category.Inference (class Inference)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Ident.Var (class Fresh, Var, fresh)
import Language.Functor.Parse (class Parse)
import Language.Functor.Type.Universe (Universe)
import Language.Parser (class LanguageParser, reserved)

data Hole :: forall k. k -> Type
data Hole a = Hole

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
  , Inject Hole typ
  ) => Inference Hole typ (Universe typ) m where
    inference Hole = pure $ hole :< inj Hole 

hole :: forall typ. Inject Hole typ => Universe typ
hole = In (deferCofree (\_ -> (hole /\ inj Hole)))

instance
  ( Monad m
  , Fresh m
  , Inject Var typ
  ) => Elimination Hole typ (Universe typ) m where
    elimination Hole t = do
       v <- fresh
       pure $ t :< inj v

instance
  ( Monad m
  , LanguageParser m
  , Functor cat
  ) => Parse Hole cat f m where
  parse = reserved "_" *> pure Hole

