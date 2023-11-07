module Language.Lambda.Inference where

import Prelude

import Control.Comonad.Cofree (Cofree, head, (:<))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (LambdaF(..), app, cat)
import Language.Lambda.Unification (class Context, class Fresh, class Rewrite, class Unification, assume, fresh, require, rewrite, unify)
import Language.Void.Value (VoidF(..))
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive)
import Matryoshka.Fold (cata)

infer :: forall exp var cat m typ .
        Monad m
     => Recursive exp (LambdaF var cat)
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unification typ m
     => Arrow typ
     => Inference var cat typ m
     => exp -> (m (Cofree (LambdaF var cat) typ)) 
infer = cata rule

rule :: forall var cat m typ .
        Monad m
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unification typ m
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

instance Inference var VoidF typ m where 
  inference (VoidF v) = absurd v

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
        => Unification typ m
        => Applicative m
        => Arrow typ
        => Fresh typ m
        => Rewrite typ m
        => Cofree (LambdaF var cat) typ
        -> Cofree (LambdaF var cat) typ
        -> m (Cofree (LambdaF var cat) typ)
appRule f a = do
  let arrTy = head f
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
 

 
 

