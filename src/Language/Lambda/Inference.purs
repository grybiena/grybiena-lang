module Language.Lambda.Inference where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (class Shadow, LambdaF(..), app, cat, shadow, var)
import Language.Lambda.Unification (class Context, class Fresh, class Rewrite, class Unify, assume, fresh, require, rewrite, unify)
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata)

infer :: forall exp var cat m typ .
        Monad m
     => IsType typ
     => Functor cat
     => Recursive exp (LambdaF var cat)
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unify typ typ m
     => Recursive typ (LambdaF var cat)
     => Corecursive typ (LambdaF var cat)
     => Arrow typ
     => Shadow var
     => Inference var cat typ m
     => exp -> (m (Cofree (LambdaF var cat) typ)) 
infer = cata rule

rule :: forall var cat m typ .
        Monad m
     => IsType typ
     => Functor cat
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unify typ typ m
     => Recursive typ (LambdaF var cat)
     => Corecursive typ (LambdaF var cat)
     => Arrow typ
     => Inference var cat typ m
     => Shadow var
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
        => Shadow var
        => var
        -> m (Cofree (LambdaF var cat) typ)
        -> m (Cofree (LambdaF var cat) typ)
absRule binding inferBody = do 
  tyBind <- fresh
  assume binding tyBind
  assume (shadow binding) tyBind 
  tyBody <- inferBody
  tyBind' <- rewrite tyBind 
  pure $ (tyBind' :->: (head tyBody)) :< (Abs binding tyBody)

class IsStar f var cat where
  isStar :: f (LambdaF var cat) -> Boolean

instance IsStar f var cat => IsType (f (LambdaF var cat)) where
  isType = isStar

class IsType typ where
  isType :: typ -> Boolean

appRule :: forall m typ var cat.
           Bind m
        => IsType typ
        => Functor cat
        => Unify typ typ m
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
      argTy = head a
  case project arrTy of
    -- Applying a type level lambda (forall)
    Abs v b | isType argTy -> do
      let argLit = flat a
      _ <- unify (var v :: typ) argLit
      tyApp <- rewrite b
      pure $ tyApp :< App f a
    -- Applying a term level arrow (a -> b)
    _ -> do
      arrArg /\ arrRet <- unifyWithArrow arrTy
      void $ unify arrArg argTy
      arrRet' <- rewrite arrRet
      pure $ arrRet' :< (App f a)
      where
        unifyWithArrow t = do
           argTy' <- fresh
           retTy <- fresh
           _ <- unify (argTy' :->: retTy) t     
           Tuple <$> rewrite argTy' <*> rewrite retTy

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

infixr 5 arrow as :->:

class ArrowObject cat where
  arrowObject :: cat 

instance
  ( ArrowObject (cat (f (LambdaF var cat)))
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  ) => Arrow (f (LambdaF var cat)) where
  arrow a b = app (app (cat arrowObject) a) b
 


