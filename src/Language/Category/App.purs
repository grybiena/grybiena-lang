module Language.Category.App where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Lit (Lit(..))
import Language.Functor.Application (class Application)
import Language.Functor.Composition (class Composition, composition)
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Reduction (infer)
import Language.Functor.Universe (Universe)
import Language.Lambda.Inference (class Arrow, unifyWithArrow)
import Language.Lambda.Unification (class Fresh, class Rewrite, class Unify, rewrite, unify)
import Matryoshka (class Corecursive, class Recursive, embed, project)


newtype App a = App (a /\ a)

instance Application App where
  app f g = App (f /\ g)
  unApp (App a) = a

instance
  ( Monad m
  , Recursive (t (Universe u t)) t
  , Fresh (Universe u t) m
  , Rewrite (Universe u t) m
  , Arrow (Universe u t) 
  , Unify (Universe u t) (Universe u t) m
  , Inject App cat 
  , Inject App t
  , Inject (Lit (Universe u t)) cat
  , Traversable t
  , Inference t t (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  ) => Inference App cat (Universe u t) m where
    inference (App (inferF /\ inferA)) = do 
      (f :: Cofree cat (Universe u t)) <- inferF
      a <- inferA
      case prj (tail a) of
        Just (Lit t) -> do
          z <- infer ((inj (App (head f /\ t))) :: t (Universe u t))
          pure $ embed z :< tail f
        Nothing -> do
          arrArg /\ arrRet <- unifyWithArrow (head f)
          void $ unify arrArg (head a)
          arrRet' <- rewrite arrRet
          pure $ arrRet' :< (inj (App (f /\ a))) 
 
instance
  ( Monad m
  , Composition cat cat t m
  , Functor cat
  ) => Elimination App cat t m where
    elimination (App (a /\ b)) t =  composition (project a) (project b) t

