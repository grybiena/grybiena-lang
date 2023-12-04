module Language.Lambda.Reduction where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Traversable (class Traversable, traverse)
import Language.Lambda.Basis (class Basis, basisB, basisC, basisI, basisK, basisS)
import Language.Lambda.Calculus (LambdaF(..), abs, app, cat, freeIn, var)
import Language.Lambda.Elimination (elimAbs)
import Language.Lambda.Inference (class IsType)
import Language.Lambda.Unification (class Context, class Fresh, class NotInScopeError, assume, fresh)
import Matryoshka (AlgebraM, CoalgebraM, hyloM)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Type.Proxy (Proxy)

class Composition f var cat m where 
  composition :: f (LambdaF var cat)
          -> f (LambdaF var cat)
          -> m (f (LambdaF var cat))

class Reduction f var cat m where
  reduction :: cat (f (LambdaF var cat))
            -> m (f (LambdaF var cat))

elimReduce :: forall t f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction f var cat m
         => Eq (f (LambdaF var cat))
         => MonadRec m
         => Ord var
         => Traversable cat
         => Functor cat
         => Basis t m f var cat
         => IsType (f (LambdaF var cat))
         => Fresh (f (LambdaF var cat)) m
         => Ord var
         => NotInScopeError var m
         => Context var (f (LambdaF var cat)) m
         => Proxy t -> f (LambdaF var cat) -> m (f (LambdaF var cat))
elimReduce p l = tailRecM go l
  where go x = do
          y <- reduce x >>= elimAbs p
          if y == x
            then pure $ Done x
            else pure $ Loop y 
 
reduce :: forall f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction f var cat m
         => Monad m
         => Traversable cat
         => Fresh (f (LambdaF var cat)) m
         => Ord var
         => NotInScopeError var m
         => Context var (f (LambdaF var cat)) m
         => f (LambdaF var cat) -> m (f (LambdaF var cat))
reduce = hyloM reduceAl reduceCo

reduceAl :: forall f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction f var cat m
         => Monad m
         => Fresh (f (LambdaF var cat)) m
         => Ord var
         => NotInScopeError var m
         => Context var (f (LambdaF var cat)) m
         => AlgebraM m (LambdaF var cat) (f (LambdaF var cat))
reduceAl =
  case _ of
    Var v -> pure $ var v
    Abs x e -> pure $ abs x e 
    App a b -> composition a b
    Cat c -> reduction c


reduceCo :: forall f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction f var cat m
         => Monad m
         => Fresh (f (LambdaF var cat)) m
         => Ord var
         => NotInScopeError var m
         => Context var (f (LambdaF var cat)) m
         => CoalgebraM m (LambdaF var cat) (f (LambdaF var cat))
reduceCo l =
  case project l of
    Var v -> pure $ Var v
    Abs x e -> do
       (t :: f (LambdaF var cat)) <- fresh
       assume x t 
       pure $ Abs x e
    App a b -> pure $ App a b
    Cat c -> pure $ Cat c




