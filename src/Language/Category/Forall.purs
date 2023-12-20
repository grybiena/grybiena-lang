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
import Language.Category.Var (class Fresh, Var(..), freshHole)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix, parseable)
import Language.Functor.Unification (class Unification)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Context, assume)
import Language.Monad.Parser (class Parser, reserved, reservedOp)
import Matryoshka (class Corecursive, embed)


newtype Forall a = Forall (Var a /\ a)

instance Show a => Show (Forall a) where
  show (Forall (v /\ a)) = "forall " <> show v <> " . " <> show a

instance Functor Forall where
  map f (Forall (v /\ a)) = Forall ((f <$> v) /\ f a)


instance Foldable Forall where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

instance Traversable Forall where
  traverse f (Forall (v /\ a)) = Forall <$> (Tuple <$> traverse f v <*> f a) 
  sequence = traverse identity

instance
  ( Monad m
  , Fresh m
  , Context Var (Universe u t) m
  , Inject Forall cat 
  , Inject Hole t
  , Inject Var t
  , Corecursive (u (Cofree t)) (Cofree t)
  ) => Inference Forall cat (Universe u t) m where
    inference (Forall (Var v /\ inferBody)) = do 
      t <- freshHole
      assume (Var v) (t :: Universe u t) 
      bod <- inferBody      
      pure (head bod :< inj (Forall (Var v /\ bod)))

instance
  ( Monad m
  ) => Unification Forall Forall t i m where
    unification _ _ = pure Nil 
else
instance
  ( Monad m
  ) => Unification Forall a t i m where
    unification _ _ = pure Nil 


instance 
  ( Monad m
  , Inject Forall cat
  ) => Elimination Forall cat typ m where
    elimination _ _ = pure Nothing 



 

instance
  ( Plus p
  ) => Postfix p Forall cat f m where
  postfix = pure empty

instance
  ( Parser m
  , Corecursive f cat
  , Parse Var cat f m 
  ) => Parse Forall cat f m where
  parse p = pure do
     reserved "forall"
     (v :: Var f) <- parseable p 
     reservedOp "."
     (c :: cat f) <- p
     pure (Forall (v /\ embed c))

