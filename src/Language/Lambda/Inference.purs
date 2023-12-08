module Language.Lambda.Inference where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Foldable (class Foldable, foldr)
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (class FreeVars, class Shadow, LambdaF(..), TermF, absMany, app, cat, free, shadow, var)
import Language.Lambda.Unification (class Context, class Fresh, class Rewrite, class Unify, assume, fresh, require, rewrite, unify)
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata)

infer :: forall exp var cat m typ .
        Monad m
     => IsTypeApp var cat typ
     => Functor cat
     => Recursive exp (TermF var cat)
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unify typ typ m
     => Recursive typ (TermF var cat)
     => Corecursive typ (TermF var cat)
     => Arrow typ
     => Shadow var
     => Inference var cat typ m
     => Ord var
     => Foldable cat
     => FreeVars var var cat
     => exp -> (m (Cofree (TermF var cat) typ)) 
infer exp = do
  u <- cata rule exp
  let q :: List var
      q = free (head u)
  pure (absMany q (head u) :< tail u)



closeTerm :: forall lam var cat.
             Corecursive lam (TermF var cat)
          => Ord var
          => Foldable cat
          => Recursive lam (TermF var cat)
          => FreeVars var var cat
          => lam -> lam
closeTerm exp = absMany (free exp) exp

rule :: forall var cat m typ .
        Monad m
     => IsTypeApp var cat typ
     => Functor cat
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unify typ typ m
     => Recursive typ (TermF var cat)
     => Corecursive typ (TermF var cat)
     => Arrow typ
     => Inference var cat typ m
     => Shadow var
     => Ord var
     => Foldable cat
     => FreeVars var var cat
     => Algebra (TermF var cat) (m (Cofree (TermF var cat) typ)) 
rule expr = 
  case expr of
    Abs b a -> absRule b a  
    App f a -> join $ appRule <$> f <*> a
    Var v -> require v >>= \t -> pure (t :< Var v)
    Cat c -> inference c 


class Inference var cat typ m where
  inference :: cat (m (Cofree (TermF var cat) typ)) -> m (Cofree (TermF var cat) typ)

absRule :: forall m typ var cat.
           Bind m
        => Fresh typ m
        => Context var typ m
        => Rewrite typ m
        => Arrow typ
        => Applicative m
        => Shadow var
        => var
        -> m (Cofree (TermF var cat) typ)
        -> m (Cofree (TermF var cat) typ)
absRule binding inferBody = do 
  tyBind <- fresh
  assume binding tyBind
  assume (shadow binding) tyBind 
  tyBody <- inferBody
  tyBind' <- rewrite tyBind 
  pure $ (tyBind' :->: (head tyBody)) :< (Abs binding tyBody)

class IsStar f abs var cat where
  isStar :: f (LambdaF abs var cat) -> Boolean

instance IsStar f abs var cat => IsType (f (LambdaF abs var cat)) where
  isType = isStar

class IsTypeApp var cat typ where
  isTypeApp :: Cofree (TermF var cat) typ -> Maybe typ

class IsType typ where
  isType :: typ -> Boolean

appRule :: forall m typ var cat.
           Bind m
        => IsTypeApp var cat typ
        => Functor cat
        => Unify typ typ m
        => Applicative m
        => Arrow typ
        => Fresh typ m
        => Rewrite typ m
        => Recursive typ (TermF var cat)
        => Corecursive typ (TermF var cat)
        => Ord var
        => Foldable cat
        => FreeVars var var cat
        => Cofree (TermF var cat) typ
        -> Cofree (TermF var cat) typ
        -> m (Cofree (TermF var cat) typ)
appRule f a = do
  let arrTy = head f
      argTy = head a
  case project (closeTerm arrTy) /\ isTypeApp a of
    -- Applying a type level lambda (forall)
    Abs v b /\ Just argLit -> do
      _ <- unify (var v :: typ) argLit
      tyApp <- rewrite b
      pure $ tyApp :< App f a
    -- Applying a term level arrow (a -> b)
    _ -> do
      arrArg /\ arrRet <- unifyWithArrow arrTy
      void $ unify arrArg argTy
      arrRet' <- rewrite arrRet
      pure $ arrRet' :< (App f a)

unifyWithArrow :: forall m exp.
                  Bind m
               => Fresh exp m
               => Unify exp exp m
               => Arrow exp
               => Rewrite exp m
               => exp -> m (Tuple exp exp)
unifyWithArrow t = do
   argTy' <- fresh
   retTy <- fresh
   _ <- unify (argTy' :->: retTy) t     
   Tuple <$> rewrite argTy' <*> rewrite retTy

flat :: forall exp typ abs var cat.
        Functor cat
     => Recursive exp (LambdaF abs var cat)
     => Corecursive exp (LambdaF abs var cat)
     => Cofree (LambdaF abs var cat) typ 
     -> exp 
flat c = embed (flat <$> tail c)


----

class Arrow typ where
  arrow :: typ -> typ -> typ

infixr 5 arrow as :->:


arrMany :: forall typ f.
           Foldable f
        => Functor f
        => Arrow typ
        => f typ -> typ -> typ
arrMany args = flip (foldr ($)) (arrow <$> args)

class ArrowObject cat where
  arrowObject :: cat 

instance
  ( ArrowObject (cat (f (LambdaF abs var cat)))
  , Corecursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
  ) => Arrow (f (LambdaF abs var cat)) where
  arrow a b = app (app (cat arrowObject) a) b
 


