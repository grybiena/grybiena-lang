module Language.Category.Forall where

import Prelude

import Control.Comonad.Cofree (Cofree, head, (:<))
import Control.Plus (class Plus, empty)
import Data.Foldable (class Foldable)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Hole (Hole)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix, parseable)
import Language.Functor.Unification (class Unification)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Context, class Variable, assume, variable)
import Language.Monad.Fresh (class Fresh, fresh, freshHole)
import Language.Monad.Parser (class Parser, reserved, reservedOp)
import Matryoshka (class Corecursive, embed)


newtype Forall var a = Forall (var a /\ a)

instance (Show a, Show (var a)) => Show (Forall var a) where
  show (Forall (v /\ a)) = "forall " <> show v <> " . " <> show a

instance (Functor var) => Functor (Forall var) where
  map f (Forall (v /\ a)) = Forall ((f <$> v) /\ f a)


instance Foldable (Forall var) where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

instance Traversable var => Traversable (Forall var) where
  traverse f (Forall (v /\ a)) = Forall <$> (Tuple <$> traverse f v <*> f a) 
  sequence = traverse identity

instance
  ( Monad m
  , Fresh (var (Cofree t (Universe u t))) m 
  , Context var (Universe u t) m
  , Inject (Forall var) cat 
  , Inject Hole t
  , Inject var t
  , Variable var
  , Corecursive (u (Cofree t)) (Cofree t)
  ) => Inference var (Forall var) cat (Universe u t) m where
    inference p (Forall (v /\ inferBody)) = do 
      t <- freshHole p
      assume (variable v) (t :: Universe u t) 
      bod <- inferBody      
      pure (head bod :< inj (Forall (variable v /\ bod)))

instance
  ( Monad m
  ) => Unification (Forall var) (Forall var) t i m where
    unification _ _ = pure Nil 
else
instance
  ( Monad m
  ) => Unification (Forall var) a t i m where
    unification _ _ = pure Nil 


instance 
  ( Monad m
  , Inject (Forall var) cat
  ) => Elimination (Forall var) cat typ m where
    elimination _ _ = pure Nothing 



 

instance
  ( Plus p
  , Functor var
  ) => Postfix p (Forall var) cat f m where
  postfix = pure empty

instance
  ( Parser m
  , Corecursive f cat
  , Parse var cat f m 
  ) => Parse (Forall var) cat f m where
  parse p = pure do
     reserved "forall"
     (v :: var f) <- parseable p 
     reservedOp "."
     (c :: cat f) <- p
     pure (Forall (v /\ embed c))

