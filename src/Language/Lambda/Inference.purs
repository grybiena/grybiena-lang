module Language.Lambda.Inference where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Except (ExceptT)
import Control.Monad.State (State)
import Data.Either (Either)
import Data.Foldable (class Foldable)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (LambdaF(..), app, cat, var)
import Language.Lambda.Unification (class Context, class Enumerable, class Fresh, class InfiniteTypeError, class NotInScopeError, class Rewrite, class Unification, class UnificationError, TypingContext, assume, fresh, require, rewrite, runUnification, unify)
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata)


runInference :: forall exp var cat err t.
        Recursive exp (LambdaF var cat)
     => Functor cat
     => Fresh (t (LambdaF var cat)) (ExceptT err (State (TypingContext var t var cat)))
     => Context var (t (LambdaF var cat)) (ExceptT err (State (TypingContext var t var cat)))
     => Rewrite (t (LambdaF var cat)) (ExceptT err (State (TypingContext var t var cat)))
     => Unification (t (LambdaF var cat)) (ExceptT err (State (TypingContext var t var cat)))
     => Arrow (t (LambdaF var cat))
     => Inference var cat (t (LambdaF var cat)) (ExceptT err (State (TypingContext var t var cat)))
     => Enumerable var
     => Ord var
     => Ord var
     => Foldable cat
     => NotInScopeError var err
     => InfiniteTypeError var (t (LambdaF var cat)) err 
     => UnificationError (t (LambdaF var cat)) err
     => Fresh var (ExceptT err (State (TypingContext var t var cat))) 
     => Unification (cat (t (LambdaF var cat))) (ExceptT err (State (TypingContext var t var cat))) 
     => Inference var cat (t (LambdaF var cat)) (ExceptT err (State (TypingContext var t var cat))) 
     => Corecursive (t (LambdaF var cat)) (LambdaF var cat)
     => Recursive (t (LambdaF var cat)) (LambdaF var cat)
     => exp -> Either err (t (LambdaF var cat)) 
runInference v = head <$> (fst $ runUnification (infer v))


infer :: forall exp var cat m typ .
        Monad m
     => Functor cat
     => Recursive exp (LambdaF var cat)
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unification typ m
     => Recursive typ (LambdaF var cat)
     => Corecursive typ (LambdaF var cat)
     => Arrow typ
     => Inference var cat typ m
     => exp -> (m (Cofree (LambdaF var cat) typ)) 
infer = cata rule

rule :: forall var cat m typ .
        Monad m
     => Functor cat
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unification typ m
     => Recursive typ (LambdaF var cat)
     => Corecursive typ (LambdaF var cat)
     => Arrow typ
     => Inference var cat typ m
     => Algebra (LambdaF var cat) (m (Cofree (LambdaF var cat) typ)) 
rule expr = 
  case expr of
    Abs b a -> absRule b a  
    App f a -> join $ appRule <$> f <*> a
    Var v -> require v >>= \t -> pure (t :< Var v)
    Cat c -> inference c


class Inference var cat typ m where
  inference :: cat (m (Cofree (LambdaF var cat) typ)) -> m (Cofree (LambdaF var cat) typ)

absRule :: forall m typ var cat.
           Bind m
        => Fresh typ m
        => Context var typ m
        => Rewrite typ m
        => Arrow typ
        => Applicative m
        => var
        -> m (Cofree (LambdaF var cat) typ)
        -> m (Cofree (LambdaF var cat) typ)
absRule binding inferBody = do 
  tyBind <- fresh
  assume binding tyBind
  tyBody <- inferBody
  tyBind' <- rewrite tyBind 
  pure $ (arrow tyBind' (head tyBody)) :< (Abs binding tyBody)


appRule :: forall m typ var cat.
           Bind m
        => Functor cat
        => Unification typ m
        => Applicative m
        => Arrow typ
        => Fresh typ m
        => Rewrite typ m
        => Recursive typ (LambdaF var cat)
        => Corecursive typ (LambdaF var cat)
        => Cofree (LambdaF var cat) typ
        -> Cofree (LambdaF var cat) typ
        -> m (Cofree (LambdaF var cat) typ)
appRule f a = do
  let arrTy = head f
  case project arrTy of
    -- Applying a type level lambda (forall)
    Abs v b -> do
      let argTy = flat a
      _ <- unify (var v) argTy
      tyApp <- rewrite b
      pure $ tyApp :< App f a
    -- Applying a term level arrow (a -> b)
    _ -> do
      arrArg /\ arrRet <- unifyWithArrow arrTy
      let argTy = head a
      void $ unify arrArg argTy
      pure $ arrRet :< (App f a)
      where
        unifyWithArrow t = do
           argTy <- fresh
           retTy <- fresh
           _ <- unify (arrow argTy retTy) t     
           Tuple <$> rewrite argTy <*> rewrite retTy

flat :: forall typ var cat.
        Functor cat
     => Recursive typ (LambdaF var cat)
     => Corecursive typ (LambdaF var cat)
     => Cofree (LambdaF var cat) typ
     -> typ
flat c = embed (flat <$> tail c)


----

class Arrow typ where
  arrow :: typ -> typ -> typ

class ArrowObject cat where
  arrowObject :: cat 

instance
  ( ArrowObject (cat (f (LambdaF var cat)))
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Arrow (f (LambdaF var cat)) where
  arrow a b = app (app (cat arrowObject) a) b
 

 
 

