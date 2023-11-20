module Language.Lambda.Elaboration where

-- The idea here is that inference is a lazily constructed
-- infinite elaboration of the expression where each node of the AST
-- is tagged with its Type (which is itself expression where each node of
-- the AST is tagged with its type...)

-- e.g. \x -> x
--   :: forall (t :: *). t -> t
--   :: * 
--   :: **
-- ...


-- but why?

import Prelude

import Control.Comonad.Cofree (Cofree, deferCofree, head, tail)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (LambdaF(..))
import Language.Lambda.Inference (class Arrow, (:->:))
import Language.Lambda.Unification (class Context, class Fresh, class Rewrite, class Shadow, class Unify, assume, fresh, require, rewrite, shadow, unify)
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata)
import Unsafe.Coerce (unsafeCoerce)

class Inference :: forall k. ((Type -> Type) -> k) -> Type -> (Type -> Type) -> (k -> Type) -> Constraint
class Inference f var cat m where
  inference :: cat (m (Elaboration f var cat)) -> m (Elaboration f var cat)

elaborate :: forall m f var cat.
           Bind m
        => Fresh (Elaboration f var cat) m
        => Context var (Elaboration f var cat) m
        => Rewrite (Elaboration f var cat) m
        => Unify (Elaboration f var cat) (Elaboration f var cat) m
        => Arrow (Elaboration f var cat)
        => Inference f var cat m
        => IsType (Elaboration f var cat)
        => Applicative m
        => Recursive (f (LambdaF var cat)) (LambdaF var cat)
        => Recursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => Corecursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => Shadow var
        => f (LambdaF var cat) -> m (Elaboration f var cat)
elaborate = cata rule

rule :: forall m f var cat.
           Bind m
        => Fresh (Elaboration f var cat) m
        => Context var (Elaboration f var cat) m
        => Rewrite (Elaboration f var cat) m
        => Unify (Elaboration f var cat) (Elaboration f var cat) m
        => Arrow (Elaboration f var cat)
        => Inference f var cat m
        => IsType (Elaboration f var cat)
        => Applicative m
        => Recursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => Corecursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => Shadow var
        => Algebra (LambdaF var cat) (m (Elaboration f var cat))
rule expr =
  case expr of
    Abs b a -> absRule b a
    App f a -> join $ appRule <$> f <*> a
    Var v -> varRule v
    Cat c -> inference c



varRule :: forall f var cat m .
           Monad m
        => Context var (Elaboration f var cat) m
        => Corecursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => var -> m (Elaboration f var cat) 
varRule v = require v >>= \t -> pure (elab $ const (t /\ Var v))


absRule :: forall m f var cat.
           Bind m
        => Fresh (Elaboration f var cat) m
        => Context var (Elaboration f var cat) m
        => Rewrite (Elaboration f var cat) m
        => Arrow (Elaboration f var cat)
        => Applicative m
        => Recursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => Corecursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => Shadow var
        => var
        -> m (Elaboration f var cat)
        -> m (Elaboration f var cat)
absRule binding inferBody = do 
  tyBind <- fresh
  assume binding tyBind
  assume (shadow binding) tyBind 
  tyBody <- inferBody
  tyBind' <- rewrite tyBind 
  pure $ elab $ const ((tyBind' :->: tyBody) /\ Abs binding (project tyBody))

class IsType typ where
  isType :: typ -> Boolean



appRule :: forall m f var cat.
           Bind m
        => Fresh (Elaboration f var cat) m
        => Context var (Elaboration f var cat) m
        => Rewrite (Elaboration f var cat) m
        => Unify (Elaboration f var cat) (Elaboration f var cat) m
        => Arrow (Elaboration f var cat)
        => IsType (Elaboration f var cat)
        => Applicative m
        => Recursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => Corecursive (f (Cofree (LambdaF var cat))) (Cofree (LambdaF var cat)) 
        => Shadow var
        => Elaboration f var cat
        -> Elaboration f var cat
        -> m (Elaboration f var cat)
appRule f a = do
  case tail $ project f of
    -- Applying a type level lambda (forall)
    Abs v b | isType a -> do
      _ <- assume v a
      tyApp <- rewrite (embed b)
      pure $ elab $ const (tyApp /\ App (project f) (project a))
    -- Applying a term level arrow (a -> b)
    _ -> do
      arrArg /\ arrRet <- unifyWithArrow f
      void $ unify arrArg a
      arrRet' <- rewrite arrRet
      pure $ elab $ const (arrRet' /\ App (project f) (project a))
      where
        unifyWithArrow :: Elaboration f var cat -> m (Elaboration f var cat /\ Elaboration f var cat)
        unifyWithArrow t = do
           argTy' <- fresh
           retTy <- fresh
           _ <- unify (argTy' :->: retTy) t     
           Tuple <$> rewrite argTy' <*> rewrite retTy






----

--instance Fresh var m => Fresh (Elaboration f var cat) m where
--  fresh = do
--     v <- fresh
--     t <- fresh --Impossible? a fresh elaboration requires an infinite sequence of fresh types
--     pure (elab (const (t /\ Var v)))

-- varRule v = require v >>= \t -> pure (elab $ const (t /\ Var v))

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

type DeferredElab f var cat = 
  Unit -> Elaboration f var cat /\ LambdaF var cat (Cofree (LambdaF var cat) (Elaboration f var cat))


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
     => DeferredElab f var cat
     -> Elaboration f var cat
elab i = embed (deferCofree i)

