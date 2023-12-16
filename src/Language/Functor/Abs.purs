module Language.Functor.Abs where

import Prelude

import Control.Comonad.Cofree (head, (:<))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Inference (class Inference)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Lambda.Inference (class Arrow, (:->:))
import Language.Lambda.Unification (class Context, class Fresh, class Rewrite, assume, fresh, rewrite)


newtype Abs abs a = Abs (abs /\ a)

instance
  ( Monad m
  , Context var typ m
  , Fresh typ m
  , Rewrite typ m
  , Arrow typ
  , Inject (Abs var) cat 
  ) => Inference (Abs var) cat typ m where
    inference (Abs (binding /\ inferBody)) = do 
      tyBind <- fresh
      assume binding tyBind
      assume binding tyBind 
      tyBody <- inferBody
      tyBind' <- rewrite tyBind 
      pure $ (tyBind' :->: (head tyBody)) :< inj (Abs (binding /\ tyBody))

