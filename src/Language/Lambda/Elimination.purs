module Language.Lambda.Elimination (class Composition, class Reduction, reduction, composition, eliminate) where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Rec.Class (class MonadRec)
import Data.Traversable (class Traversable)
import Data.Tuple (fst)
import Effect.Class (class MonadEffect)
import Language.Lambda.Basis (class Basis, basisB, basisC, basisI, basisK, basisS)
import Language.Lambda.Calculus (class FreeVars, class Shadow, LambdaF(..), flat, freeIn, var)
import Language.Lambda.Elimination.Algebra (EliminationAlgebra(..))
import Language.Lambda.Inference (class ArrowObject, class Inference, class IsTypeApp, appRule, closeTerm, unifyWithArrow, (:->:))
import Language.Lambda.Judgement (class Reasoning)
import Language.Lambda.Unification (class Context, class Fresh, class NotInScopeError, class Skolemize, class Substitute, class Unify)
import Language.Lambda.Unification.Error (class ThrowUnificationError)
import Matryoshka (AlgebraM, CoalgebraM, hyloM)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive)
import Type.Proxy (Proxy)

eliminate :: forall f var cat t m.
             Recursive (f (LambdaF var var cat)) (LambdaF var var cat) 
          => Corecursive (f (LambdaF var var cat)) (LambdaF var var cat) 
          => Ord var
          => Traversable cat
          => Functor cat
          => Basis t m f var cat
          => MonadRec m
          => MonadEffect m
          => Fresh Int m
          => Fresh var m
          => Fresh (f (LambdaF var var cat)) m
          => Shadow var
          => Skolemize f var cat
          => Substitute var cat f m
          => Unify (cat (f (LambdaF var var cat))) (cat (f (LambdaF var var cat))) m
          => Unify var (f (LambdaF var var cat)) m
          => ThrowUnificationError (f (LambdaF var var cat)) m 
          => ArrowObject (cat (f (LambdaF var var cat))) 
          => NotInScopeError var m
          => Context var (f (LambdaF var var cat)) m
          => Inference var var cat (f (LambdaF var var cat)) m 
          => IsTypeApp var var cat (f (LambdaF var var cat))
          => Eq (f (LambdaF var var cat))
          => Composition f var cat m
          => Reduction f var cat m
          => FreeVars var var cat
          => Reasoning f var var cat m
          => Proxy t
          -> Cofree (LambdaF var var cat) (f (LambdaF var var cat))
          -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))
eliminate p = hyloM catamorphism anamorphism 
  where
    anamorphism :: CoalgebraM m (EliminationAlgebra var cat (f (LambdaF var var cat)))
                                (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))
    anamorphism l =
      case tail l of
        Var v -> pure $ VarRule v (head l) 
        App a b -> pure $ AppRule (head l) a b 
        Abs x e ->
          case tail e of
            Var v | v == x -> pure BasisI
            Abs _ f | x `freeIn` (flat f :: f (LambdaF var var cat)) -> pure $ AbsRule (head l) x e
            App a b | (flat b :: f (LambdaF var var cat)) == var x
                    && (not (x `freeIn` (flat a :: f (LambdaF var var cat))))-> pure $ EtaReduce a
            App e1 e2 | x `freeIn` (flat e1 :: f (LambdaF var var cat))
                        && x `freeIn` (flat e2 :: f (LambdaF var var cat)) -> do
                      art <- unifyWithArrow (head l)
                      let typ = fst art
                          t1 = (closeTerm $ typ :->: head e1) :< Abs x e1
                          t2 = (closeTerm $ typ :->: head e2) :< Abs x e2
                      pure $ BasisS t1 t2
            App e1 e2 | x `freeIn` (flat e1 :: f (LambdaF var var cat)) -> do
                      art <- unifyWithArrow (head l)
                      let typ = fst art
                          t1 = (closeTerm $ typ :->: head e1) :< Abs x e1
                      pure $ BasisC t1 e2
            App e1 e2 | x `freeIn` (flat e2 :: f (LambdaF var var cat)) -> do
                      art <- unifyWithArrow (head l)
                      let typ = fst art
                          t2 = (closeTerm $ typ :->: head e2) :< Abs x e2
                      pure $ BasisB e1 t2
            Cat _ | x `freeIn` (flat e :: f (LambdaF var var cat)) -> pure $ AbsRule (head l) x e
            _ -> pure $ BasisK e
        Cat c -> pure $ CatRule (head l) c
    
    catamorphism :: AlgebraM m (EliminationAlgebra var cat (f (LambdaF var var cat)))
                               (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))
    catamorphism =
      case _ of
        VarRule v t -> pure $ t :< Var v
        AppRule typ a b -> composition a b typ
        BasisK e -> do
           k <- basisK p
           appRule k e 
        BasisI -> do
           basisI p
        AbsRule typ x e -> do
           pure $ typ :< Abs x e
        BasisS e1 e2 -> do
           s <- basisS p
           o <- appRule s e1
           appRule o e2
        BasisC e1 e2 -> do
           c <- basisC p
           i <- appRule c e1
           appRule i e2
        BasisB e1 e2 -> do
           b <- basisB p
           i <- appRule b e1
           appRule i e2
        EtaReduce e -> do
           pure e 
        CatRule typ c -> do
           reduction c typ 

class Composition f var cat m where 
  composition :: (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))
              -> (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))
              -> (f (LambdaF var var cat))
              -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))
 

class Reduction f var cat m where
  reduction :: cat (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))
            -> (f (LambdaF var var cat))
            -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))



