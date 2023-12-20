module Language.Category.App where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Foldable (class Foldable)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Functor.Application (class Application)
import Language.Functor.Composition (class Composition, composition)
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Unification (class Unification, unification, unify)
import Language.Functor.Universe (Universe)
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
  ( Monad m
  , Inject App cat 
  , Inject App t
  , Unification t t (Cofree t (Universe u t)) Maybe
--  , Inference cat cat (Universe u t) m
--  , Unify (Universe u t) m
  , Functor t
  , Unification t t (Cofree t (Universe u t)) m
  , Recursive (u (Cofree t)) (Cofree t)
--  , Corecursive (u t) t
--  , Recursive (u t) t
  , Rewrite (Universe u t) m
  ) => Inference App cat (Universe u t) m where
    inference (App (inferF /\ inferA)) = do 
      (f :: Cofree cat (Universe u t)) <- inferF
      a <- inferA
      let unifyWithArrow = unsafeCoerce unit
      arrArg /\ arrRet <- unifyWithArrow (head f)
      unify (arrArg) (head a)
      arrRet' <- rewrite arrRet
      pure $ arrRet' :< (inj (App (f /\ a))) 

instance
  ( Monad m
  ) => Unification App App i m where 
    unification (App (a /\ b)) (App (c /\ d)) = pure $ List.fromFoldable [(a /\ c), (b /\ d)] 


--       case prj c of
--         Just (App (c /\ d)) -> do
--            pure unit
--            unify a c
----            unify (project $ head a) (project $ head c)
----            unify (project $ head b) (project $ head d)
--
--         Nothing -> unsafeCoerce unit
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

