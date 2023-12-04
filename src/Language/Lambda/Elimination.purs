module Language.Lambda.Elimination (elimination) where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Control.Monad.Rec.Class (class MonadRec)
import Data.Traversable (class Traversable)
import Language.Lambda.Basis (class Basis, basisB, basisC, basisI, basisK, basisS)
import Language.Lambda.Calculus (LambdaF(..), abs, app, cat, freeIn, var)
import Language.Lambda.Elimination.Algebra (EliminationAlgebra(..))
import Language.Lambda.Inference (class IsType)
import Matryoshka (AlgebraM, CoalgebraM, hyloM)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Type.Proxy (Proxy)

elimination :: forall f var cat t m.
               Recursive (f (LambdaF var cat)) (LambdaF var cat) 
            => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
            => Ord var
            => Traversable cat
            => Functor cat
            => Basis t m f var cat
            => MonadRec m
            => IsType (f (LambdaF var cat))
            => Eq (f (LambdaF var cat))
            => Proxy t
            -> f (LambdaF var cat)
            -> m (f (LambdaF var cat))
elimination p = hyloM catamorphism anamorphism 
  where
    anamorphism :: CoalgebraM m (EliminationAlgebra var cat) (f (LambdaF var cat))
    anamorphism l =
      case project l of
        Var v -> pure $ VarRule v 
        App a b -> pure $ AppRule a b 
        Abs x e ->
          case project e of
            Var v | v == x -> pure BasisI
            Abs _ f | x `freeIn` f -> pure $ AbsRule x e
            App a b | b == var x && (not (x `freeIn` a))-> pure $ EtaReduce a
            App e1 e2 | x `freeIn` e1 && x `freeIn` e2 -> pure $ BasisS x e1 e2
            App e1 e2 | x `freeIn` e1 -> pure $ BasisC x e1 e2
            App e1 e2 | x `freeIn` e2 -> pure $ BasisB x e1 e2
            Cat _ | x `freeIn` e -> pure $ AbsRule x e
            _ -> pure $ BasisK e
        Cat c -> pure $ CatRule c
    
    catamorphism :: AlgebraM m (EliminationAlgebra var cat) (f (LambdaF var cat))
    catamorphism =
      case _ of
        VarRule v -> pure $ var v
        AppRule a b -> pure $ app a b
        BasisK e -> flip app e <$> basisK p
        BasisI -> basisI p
        AbsRule x e -> pure $ abs x e
        BasisS x e1 e2 -> (\s -> app (app s (abs x e1)) (abs x e2)) <$> basisS p
        BasisC x e1 e2 -> (\c -> app (app c (abs x e1)) e2) <$> basisC p
        BasisB x e1 e2 -> (\b -> app (app b e1) (abs x e2)) <$> basisB p
        EtaReduce e -> pure e 
        CatRule c -> pure $ cat c


