module Language.Category.App where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Rec.Class (class MonadRec)
import Data.Foldable (class Foldable)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Debug (traceM)
import Language.Category.Arrow (Arrow, unifyWithArrow)
import Language.Category.Hole (Hole)
import Language.Category.Var (class Fresh, Var, freshHole)
import Language.Functor.Application (class Application)
import Language.Functor.Composition (class Composition, composition)
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Unification (class Unification, unification, unify)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Context)
import Language.Monad.Parser (class Parser)
import Language.Monad.Rewrite (class Rewrite, rewrite)
import Matryoshka (class Corecursive, class Recursive, embed, project)
import Unsafe.Coerce (unsafeCoerce)


newtype App a = App (a /\ a)

instance Show a => Show (App a) where
  show (App (a /\ b)) = "(" <> show a <> " " <> show b <> ")"

instance Application App where
  app f g = App (f /\ g)
  unApp (App a) = a

instance Functor App where
  map f (App (a /\ b)) = App (f a /\ f b)

instance Foldable App where
  foldr f b (App (x /\ y)) = f x (f y b) 
  foldl f b (App (x /\ y)) = f (f b x) y 
  foldMap f (App (x /\ y)) = f x <> f y

instance Traversable App where
  traverse f (App (x /\ y)) = App <$> (Tuple <$> f x <*> f y)
  sequence = traverse identity

instance
  ( MonadRec m
  , Inject App cat 
  , Inject App t
  , Unification t t (Cofree t (Universe u t)) m 
  , Fresh m
  , Functor t
  , Unification t t (Cofree t (Universe u t)) m
  , Recursive (u (Cofree t)) (Cofree t)
  , Inject Arrow t
  , Inject Var t
  , Inject Hole t
  , Traversable t
  , Context Var (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  , Rewrite (Universe u t) m
  ) => Inference App cat (Universe u t) m where
    inference (App (inferF /\ inferA)) = do 
      (f :: Cofree cat (Universe u t)) <- inferF
      a <- inferA
      arrArg /\ arrRet <- unifyWithArrow (head f)
      unify (arrArg) (head a)
      arrRet' <- rewrite arrRet
      pure $ arrRet' :< (inj (App (f /\ a))) 

instance
  ( Monad m
  ) => Unification App App i m where 
    unification (App (a /\ b)) (App (c /\ d)) = pure $ List.fromFoldable [(a /\ c), (b /\ d)] 

else 
instance
  ( Monad m
  ) => Unification App a i m where
    unification (App (a /\ b)) c = pure Nil

instance
  ( Monad m
  , Composition App cat cat t m
  , Functor cat
  ) => Elimination App cat t m where
    elimination (App (a /\ b)) t =  Just <$> composition (project a) (project b) t

instance
  ( Monad m
  , Corecursive f cat
  , Applicative p
  ) => Postfix p App cat f m where 
  postfix p = pure $ \f -> App <<< Tuple (embed f) <<< embed <$> p 

instance
  ( Parser m
  , Alt m
  ) => Parse App cat f m where
  parse = const Nothing 

