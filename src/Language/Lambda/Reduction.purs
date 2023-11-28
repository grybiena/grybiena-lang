module Language.Lambda.Reduction where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Data.Traversable (class Traversable, traverse)
import Language.Lambda.Basis (class Basis, basisB, basisC, basisI, basisK, basisS)
import Language.Lambda.Calculus (LambdaF(..), abs, app, cat, freeIn, var)
import Language.Lambda.Inference (class IsType)
import Matryoshka.Algebra (AlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cataM)
import Type.Proxy (Proxy)

class Composition f var cat m where 
  composition :: f (LambdaF var cat)
          -> f (LambdaF var cat)
          -> m (f (LambdaF var cat))

class Reduction :: forall k. k -> ((Type -> Type) -> Type) -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class Reduction t f var cat m where
  reduction :: Proxy t
            -> cat (f (LambdaF var cat))
            -> m (f (LambdaF var cat))
 
composer :: forall t f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction t f var cat m
         => Eq (f (LambdaF var cat))
         => Monad m
         => Traversable cat
         => Proxy t -> f (LambdaF var cat) -> m (f (LambdaF var cat))
composer p = cataM (composeLambda p)

composeLambda :: forall t f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction t f var cat m
         => Applicative m
         => Proxy t -> AlgebraM m (LambdaF var cat) (f (LambdaF var cat))
composeLambda _ =
  case _ of
    Var v -> pure $ var v
    Abs x e -> pure $ abs x e
    App a b -> composition a b
    Cat c -> pure $ cat c 

reduce :: forall t f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction t f var cat m
         => Eq (f (LambdaF var cat))
         => Monad m
         => Traversable cat
         => Proxy t -> f (LambdaF var cat) -> m (f (LambdaF var cat))
reduce p = cataM (reduceLambda p)

reduceLambda :: forall t f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction t f var cat m
         => Applicative m
         => Proxy t -> AlgebraM m (LambdaF var cat) (f (LambdaF var cat))
reduceLambda p =
  case _ of
    Var v -> pure $ var v
    Abs x e -> pure $ abs x e
    App a b -> composition a b
    Cat c -> reduction p c

-- Annotated with rules described here https://en.wikipedia.org/wiki/Combinatory_logic#Combinators_B,_C
elimAbs :: forall f var cat t m.
          Recursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Ord var
       => Traversable cat
       => Functor cat
       => Basis t m f var cat
       => Monad m
       => IsType (f (LambdaF var cat))
       => Eq (f (LambdaF var cat))
       => Proxy t
       -> f (LambdaF var cat)
       -> m (f (LambdaF var cat))
elimAbs p lam = 
  case project lam of
    -- 1. T[x] ⇒ x
    Var v -> pure (var v)
    -- 2. T[(E₁ E₂)] ⇒ (T[E₁] T[E₂])
    App a b -> app <$> elimAbs p a <*> elimAbs p b
    Abs x e ->
      case project e of
        -- 4. T[λx.x] ⇒ I
        Var v | v == x -> basisI p
        -- 5. T[λx.λy.E] ⇒ T[λx.T[λy.E]] (if x is free in E)
        Abs _ f | x `freeIn` f -> abs x <$> elimAbs p e
        -- eta reduction. T[λx.a x] ⇒ T[a]
        App a b | b == var x && (not (x `freeIn` a))-> elimAbs p a
        -- 6. T[λx.(E₁ E₂)] ⇒ (S T[λx.E₁] T[λx.E₂]) (if x is free in both E₁ and E₂)
        App e1 e2 | x `freeIn` e1 && x `freeIn` e2 -> do
                s <- basisS p
                f <- app s <$> (elimAbs p (abs x e1))
                app f <$> (elimAbs p (abs x e2))
        -- 7. T[λx.(E₁ E₂)] ⇒ (C T[λx.E₁] T[E₂]) (if x is free in E₁ but not E₂)
        App e1 e2 | x `freeIn` e1 -> do
                c <- basisC p
                f <- app c <$> (elimAbs p (abs x e1))
                app f <$> (elimAbs p e2)
        -- 8. T[λx.(E₁ E₂)] ⇒ (B T[E₁] T[λx.E₂]) (if x is free in E₂ but not E₁)
        App e1 e2 | x `freeIn` e2 -> do
                b <- basisB p
                f <- app b <$> (elimAbs p e1)
                app f <$> (elimAbs p (abs x e2))
        -- cat reduction.  T[λx. o] ⇒ λx.T[o]
        Cat _ | x `freeIn` e -> abs x <$> elimAbs p e
        -- 3. T[λx.E] ⇒ (K T[E]) (if x is not free in E)
        _ -> do
           k <- basisK p
           app k <$> (elimAbs p e)
    Cat c -> cat <$> (traverse (elimAbs p) c)

