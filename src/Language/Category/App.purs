module Language.Category.App where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Lit (Lit(..))
import Language.Functor.Application (class Application)
import Language.Functor.Composition (class Composition, composition)
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Reduction (infer)
import Language.Functor.Universe (Universe)
import Language.Lambda.Inference (class Arrow, unifyWithArrow)
import Language.Lambda.Unification (class Fresh, class Rewrite, class Unify, rewrite, unify)
import Language.Monad.Parser (class Parser, fail)
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
  , Functor cat
--  , Recursive (t (Universe u t)) t
--  , Fresh (Universe u t) m
--  , Rewrite (Universe u t) m
--  , Arrow (Universe u t) 
--  , Unify (Universe u t) (Universe u t) m
--  , Inject App cat 
--  , Inject App t
--  , Inject (Lit (Universe u t)) cat
--  , Traversable t
--  , Inference t t (Universe u t) m
--  , Corecursive (u (Cofree t)) (Cofree t)
  ) => Inference App cat (Universe u t) m where
    inference (App (inferF /\ inferA)) = do 
       unsafeCoerce unit
--      (f :: Cofree cat (Universe u t)) <- inferF
--      a <- inferA
--      case prj (tail a) of
--        Just (Lit t) -> do
--          z <- infer ((inj (App (head f /\ t))) :: t (Universe u t))
--          pure $ embed z :< tail f
--        Nothing -> do
--          arrArg /\ arrRet <- unifyWithArrow (head f)
--          void $ unify arrArg (head a)
--          arrRet' <- rewrite arrRet
--          pure $ arrRet' :< (inj (App (f /\ a))) 
 
instance
  ( Monad m
  , Composition App cat cat t m
  , Functor cat
  ) => Elimination App cat t m where
    elimination (App (a /\ b)) t =  composition (project a) (project b) t

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

