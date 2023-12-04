module Language.Lambda.Reduction where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Traversable (class Traversable, traverse)
import Language.Lambda.Basis (class Basis, basisB, basisC, basisI, basisK, basisS)
import Language.Lambda.Calculus (LambdaF(..), abs, app, cat, freeIn, var)
import Language.Lambda.Inference (class IsType)
import Language.Lambda.Unification (class Context, class Fresh, class NotInScopeError, assume, fresh)
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
         => Fresh (f (LambdaF var cat)) m
         => Ord var
         => NotInScopeError var m
         => Context var (f (LambdaF var cat)) m
         => f (LambdaF var cat) -> m (f (LambdaF var cat))
reduce l =
  case project l of
    Var v -> pure $ var v
    Abs x e -> do
       (t :: f (LambdaF var cat)) <- fresh
       assume x t
       e' <- reduce e
       pure $ abs x e'
    App a b -> do
       a' <- reduce a
       b' <- reduce b
       composition a' b'
    Cat c -> reduction c

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


