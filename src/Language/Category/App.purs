module Language.Category.App where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, head, (:<))
import Control.Comonad.Env (EnvT(..))
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Foldable (class Foldable)
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Arrow (Arrow, unifyWithArrow)
import Language.Category.Hole (Hole)
import Language.Functor.Application (class Application)
import Language.Functor.Composition (class Composition, composition)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Unification (class Unification, class UnificationError, Layer, unificationError, unify)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Rewrite, class Subtext, rewrite)
import Language.Monad.Fresh (class Fresh)
import Language.Monad.Parser (class Parser)
import Matryoshka (class Corecursive, class Recursive, embed, project)
import Type.Proxy (Proxy(..))


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
  , Unification t t (Universe u t) (Cofree t (Universe u t)) m 
  , Fresh (var (Cofree t (Universe u t))) m 
  , Functor t
  , Recursive (u (Cofree t)) (Cofree t)
  , Inject Arrow t
  , Inject var t
  , Inject Hole t
  , Traversable t
  , Subtext var (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  , Rewrite var (Universe u t) m
  ) => Inference var App cat (Universe u t) m where
    inference p (App (inferF /\ inferA)) = do 
      (f :: Cofree cat (Universe u t)) <- inferF
      a <- inferA
      arrArg /\ arrRet <- unifyWithArrow p (head f)
      unify (arrArg) (head a)
      arrRet' <- rewrite (Proxy :: Proxy var) arrRet
      pure $ arrRet' :< (inj (App (f /\ a))) 

instance
  ( Monad m
  , Recursive (u (Cofree t)) (Cofree t)
  ) => Unification App App (Universe u t) (Cofree t (Universe u t)) m where 
    unification (EnvT (ta /\ App (a /\ b))) (EnvT (tb /\ App (c /\ d))) = do
       pure $ List.fromFoldable [(project ta /\ project tb),(a /\ c), (b /\ d)] 

else 
instance
  ( Monad m
  , UnificationError (Layer App u t) (Layer q u t) err 
  , MonadThrow err m
  ) => Unification App q (Universe u t) (Cofree t (Universe u t)) m where
    unification a b = throwError $ unificationError a b 

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

