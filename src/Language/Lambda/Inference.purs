module Language.Lambda.Inference where

import Prelude

import Control.Comonad.Cofree (Cofree, head, (:<))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (class Rewrite, class Substitute, LambdaF(..), abs, app, cat, rewrite, substitute, var)
import Language.Void.Value (VoidF(..))
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata)

infer :: forall exp var cat m typ .
        Monad m
     => Recursive exp (LambdaF var cat)
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unify typ m
     => Arrow typ
     => CatRule var cat typ m
     => exp -> (m (Cofree (LambdaF var cat) typ)) 
infer = cata rule

rule :: forall var cat m typ .
        Monad m
     => Fresh typ m
     => Context var typ m
     => Rewrite typ m
     => Unify typ m
     => Arrow typ
     => CatRule var cat typ m
     => Algebra (LambdaF var cat) (m (Cofree (LambdaF var cat) typ)) 
rule expr = 
  case expr of
    Abs b a -> absRule b a  
    App f a -> join $ appRule <$> f <*> a
    Var v -> require v >>= \t -> pure (t :< Var v)
    Cat c -> catRule c


class CatRule var cat typ m where
  catRule :: cat (m (Cofree (LambdaF var cat) typ)) -> m (Cofree (LambdaF var cat) typ)

instance CatRule var VoidF typ m where 
  catRule (VoidF v) = absurd v

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
        => Unify typ m
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
 

class Context var typ m | var -> typ where
  assume :: var -> typ -> m Unit
  require :: var -> m typ

class Fresh :: Type -> (Type -> Type) -> Constraint
class Fresh typ m where
  fresh :: m typ


class Unify typ m where
  unify :: typ -> typ -> m typ

class UnificationError typ m where
  unificationError :: typ -> typ -> m typ

instance
  ( Monad m
  , Fresh var m 
  , Eq var
  , Substitute var cat f m 
  , Rewrite (f (LambdaF var cat)) m 
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , Unify (cat (f (LambdaF var cat))) m
  , UnificationError (f (LambdaF var cat)) m
  ) => Unify (f (LambdaF var cat)) m where
  unify ta tb = do
     case project ta /\ project tb of
       Var a /\ Var b | a == b -> pure ta
       Var a /\ _ -> substitute a tb *> pure tb
       _ /\ Var b -> substitute b ta *> pure ta
       Abs ab aa /\ Abs bb ba -> do
         qv <- fresh
         let qty :: f (LambdaF var cat)
             qty = var qv
         substitute ab qty
         substitute bb qty
         ar <- rewrite aa
         br <- rewrite ba
         abs qv <$> unify ar br
       App ab aa /\ App bb ba -> do
         app <$> unify ab bb <*> unify aa ba
       Cat ca /\ Cat cb -> cat <$> unify ca cb
       _ -> unificationError ta tb

  
 

