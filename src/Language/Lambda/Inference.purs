module Language.Lambda.Inference where

import Prelude

import Control.Comonad.Cofree (Cofree, deferCofree, head, tail, (:<))
import Control.Monad.Except (ExceptT)
import Control.Monad.State (State)
import Data.Either (Either)
import Data.Foldable (class Foldable)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested (type (/\), (/\))
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
     => IsType (t (LambdaF var cat))
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
     => IsType typ
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
     => IsType typ
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
      argTy = head a
  case project arrTy of
    -- Applying a type level lambda (forall)
    Abs v b | isType argTy -> do
      let argLit = flat a
      _ <- unify (var v) argLit
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
 

 
-- Elaboration of ininite inference 
---- 
-- type Elaboration f var cat
-- represents the infinite elaboration of the inference homomorphism
-- where `level` extracts the term at the current level
-- and `ascend` lifts the elaboration to the next level

-- i.e term ~ level <$> infer term 
--     type ~ level <<< ascend <$> infer term
--     kind ~ level <<< ascend <<< ascend <$> infer term

-- and so on...

-- a well typed term should converge on the infinite sequence of Stars

-- the question is can we lazily create a value of type Elaboration f var cat...

type Elaboration :: forall k. ((Type -> Type) -> k) -> Type -> (Type -> Type) -> k
type Elaboration f var cat = f (Cofree (LambdaF var cat))

level :: forall f var cat.
        Functor cat
     => Recursive (f (LambdaF var cat)) (LambdaF var cat)
     => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
     => Recursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat))
     => Corecursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat))
     => Elaboration f var cat
     -> f (LambdaF var cat) 
level c = embed ((level <<< embed) <$> (tail (project c)))
 
ascend :: forall f var cat.
        Functor cat
     => Recursive (f (LambdaF var cat)) (LambdaF var cat)
     => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
     => Recursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat))
     => Corecursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat))
     => Elaboration f var cat 
     -> Elaboration f var cat
ascend = head <<< project



--deferCofree :: forall f a. (Unit -> Tuple a (f (Cofree f a))) -> Cofree f a

elab :: forall f var cat .
        Corecursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat))
     => (Unit -> Elaboration f var cat /\ LambdaF var cat (Cofree (LambdaF var cat) (Elaboration f var cat)))
     -> Elaboration f var cat
elab i = embed (deferCofree i)

