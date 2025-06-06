module Language.Category.Arrow where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, head, (:<))
import Control.Comonad.Env (EnvT(..))
import Control.Monad.Rec.Class (class MonadRec)
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Hole (Hole)
import Language.Category.Level (Level, toInfinity)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Unification (class Unification, unify)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Subtext, rewrite)
import Language.Monad.Fresh (class Fresh, freshHole)
import Language.Monad.Parser (class Parser, reservedOp)
import Matryoshka (class Corecursive, class Recursive, embed, project)
import Type.Proxy (Proxy)

data Arrow a = Arrow (a /\ a)


derive instance Generic (Arrow a) _

instance Show a => Show (Arrow a) where
  show = genericShow

instance Functor Arrow where
  map f (Arrow (a /\ b)) = Arrow (f a /\ f b)

instance Foldable Arrow where
  foldr f b (Arrow (x /\ y)) = f x (f y b) 
  foldl f b (Arrow (x /\ y)) = f (f b x) y 
  foldMap f (Arrow (x /\ y)) = f x <> f y

instance Traversable Arrow where
  traverse f (Arrow (x /\ y)) = Arrow <$> (Tuple <$> f x <*> f y)
  sequence = traverse identity

instance
  ( Monad m
  , Corecursive f cat
  , Applicative p
  , Parser m
  ) => Postfix p Arrow cat f m where 
  postfix p = pure $ \f -> reservedOp "->" *> (Arrow <<< Tuple (embed f) <<< embed <$> p)

instance
  ( Parser m
  , Alt m
  ) => Parse Arrow cat f m where
  parse = const Nothing 


instance
  ( MonadRec m 
  , Inject Arrow typ 
  , Inject Level typ
  , Unification typ typ (Universe u typ) (Cofree typ (Universe u typ)) m
  , Corecursive (u (Cofree typ)) (Cofree typ)
  , Recursive (u (Cofree typ)) (Cofree typ)
  ) => Inference var Arrow typ (Universe u typ) m where
    inference _ (Arrow (inferA /\ inferB)) = do 
       a <- inferA
       unify (toInfinity 1 :: Universe u typ) (head a)
       b <- inferB
       unify (toInfinity 1 :: Universe u typ) (head b)
       -- TODO take the max level of a /\ b
       pure $ toInfinity 1 :< inj (Arrow (a /\ b))

instance
  ( Monad m
  , Recursive (u (Cofree t)) (Cofree t)
  ) => Unification Arrow Arrow (Universe u t) (Cofree t (Universe u t)) m where
    unification (EnvT (ta /\ Arrow (a /\ b))) (EnvT (tb /\ Arrow (c /\ d))) = do
      pure $ List.fromFoldable [(project ta /\ project tb), (a /\ c), (b /\ d)]
else 
instance
  ( Monad m
  ) => Unification a Arrow t i m where
    unification _ _ = pure Nil
else 
instance
  ( Monad m
  ) => Unification Arrow a t i m where
    unification _ _ = pure Nil


instance (Applicative m) => Elimination Arrow cat t m where
  elimination _ _ = pure Nothing

unifyWithArrow :: forall var u t m.
                  MonadRec m
               => Fresh (var (Cofree t (Universe u t))) m 
               => Inject Hole t
               => Unification t t (Universe u t) (Cofree t (Universe u t)) m
               => Recursive (u (Cofree t)) (Cofree t)
               => Corecursive (u (Cofree t)) (Cofree t)
               => Inject Arrow t
               => Inject var t
               => Traversable t
               => Subtext var (Universe u t) m 
               => Proxy var -> Universe u t -> m (Universe u t /\ Universe u t)
unifyWithArrow p t = do
  a <- freshHole p
  b <- freshHole p
  c <- freshHole p
  unify (embed (c :< inj (Arrow (project a /\ project b))) :: Universe u t) t
  Tuple <$> rewrite p a <*> rewrite p b

