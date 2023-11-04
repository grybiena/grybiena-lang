module Language.Lambda.Infer where

import Prelude

import Control.Applicative (class Applicative)
import Control.Comonad (class Comonad)
import Control.Monad (class Monad)
import Data.Identity (Identity)
import Data.Traversable (class Traversable)
import Language.Lambda.Calculus (LambdaF(..))
import Language.Void.Value (Value, VoidF)
import Matryoshka.Algebra (GAlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (GCoalgebraM, CoalgebraM)
import Matryoshka.DistributiveLaw (distApplicative)
import Matryoshka.Fold (gcataM)
import Matryoshka.Unfold (anaM, ganaM)

class InferAbs :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class InferAbs pat typ juj m where
  inferAbs :: pat -> juj typ -> m typ

class InferApp :: Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class InferApp typ juj m where
  inferApp :: juj typ -> juj typ -> m typ

class InferVar :: Type -> Type -> (Type -> Type) -> Constraint
class InferVar var ty m where
  inferVar :: var -> m ty

class InferCat :: (Type -> Type) -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class InferCat cat typ juj m where
  inferCat :: cat (juj typ) -> m typ

inference :: forall m pat var cat exp juj typ.
             Recursive exp (LambdaF pat var cat)
          => Monad m
          => Comonad juj
          => Traversable cat
          => Traversable juj
          => Applicative juj
          => InferAbs pat typ juj m
          => InferApp typ juj m
          => InferVar var typ m
          => InferCat cat typ juj m
          => exp -> m typ
inference = gcataM distApplicative go
  where
    go :: GAlgebraM juj m (LambdaF pat var cat) typ
    go (Abs p e) = inferAbs p e
    go (App f a) = inferApp f a
    go (Var v) = inferVar v
    go (Cat c) = inferCat c


class InferAbs' pat exp typ m n where
  inferAbs' :: pat -> exp -> m (typ (n exp))

class InferApp' exp typ m n where
  inferApp' :: exp -> exp -> m (typ (n exp))

class InferVar' var exp typ m n where
  inferVar' :: var -> m (typ (n exp))

class InferCat' cat exp typ m n where
  inferCat' :: cat exp -> m (typ (n exp))

class Judgement exp juj typ m | exp -> juj where
  judgement :: juj exp -> m (typ (juj exp))

data Judge typ exp =
  JudgeApp exp exp -- (typ (Judge typ exp)) exp (typ (Judge typ exp)) (typ (Judge typ exp)) 

instance Monad m => InferApp' Value (LambdaF String String VoidF) m (Judge (LambdaF String String VoidF)) where
  inferApp' a b = pure $ Var ""



infero' :: forall pat var cat exp tvar tcat juj typ m.
         Judgement exp juj (LambdaF tvar tvar tcat) m
      => Recursive exp (LambdaF pat var cat)
      => Corecursive typ (LambdaF tvar tvar tcat)
      => Applicative (LambdaF tvar tvar tcat)
      => InferAbs' pat exp (LambdaF tvar tvar tcat) m juj
      => InferApp' exp (LambdaF tvar tvar tcat) m juj 
      => InferVar' var exp (LambdaF tvar tvar tcat) m juj
      => InferCat' cat exp (LambdaF tvar tvar tcat) m juj
      => Traversable tcat
      => Monad m
      => Monad juj
      => Traversable juj
      => exp -> m typ

infero' = ganaM distApplicative infer'

infer' :: forall pat var cat exp tvar tcat juj typ m.
         Judgement exp juj (LambdaF tvar tvar tcat) m
      => Recursive exp (LambdaF pat var cat)
      => InferAbs' pat exp (LambdaF tvar tvar tcat) m juj
      => InferApp' exp (LambdaF tvar tvar tcat) m juj 
      => InferVar' var exp (LambdaF tvar tvar tcat) m juj 
      => InferCat' cat exp (LambdaF tvar tvar tcat) m juj 
      => GCoalgebraM juj m (LambdaF tvar tvar tcat) exp
infer' exp =
  case project exp of
    Abs b a -> inferAbs' b a
    App f a -> inferApp' f a
    Var v -> inferVar' v
    Cat c -> inferCat' c

class InferAbs'' pat exp juj m where
  inferAbs'' :: pat -> exp -> m (juj exp)

class InferApp'' exp juj m where
  inferApp'' :: exp -> exp -> m (juj exp)

class InferVar'' var exp juj m where
  inferVar'' :: var -> m (juj exp)

class InferCat'' cat exp juj m where
  inferCat'' :: cat exp -> m (juj exp)

infero :: forall typ juj m exp pat var cat.
          Corecursive typ juj
       => Monad m
       => Traversable juj
       => Recursive exp (LambdaF pat var cat)
       => InferAbs'' pat exp juj m
       => InferApp'' exp juj m
       => InferVar'' var exp juj m
       => InferCat'' cat exp juj m
       => exp -> m typ
infero = anaM infer

infer :: forall m juj exp pat var cat .
         Recursive exp (LambdaF pat var cat)   
      => InferAbs'' pat exp juj m 
      => InferApp'' exp juj m
      => InferVar'' var exp juj m
      => InferCat'' cat exp juj m
      => CoalgebraM m juj exp
infer exp =
  case project exp of
    Abs b a -> inferAbs'' b a
    App f a -> inferApp'' f a
    Var v -> inferVar'' v
    Cat c -> inferCat'' c



