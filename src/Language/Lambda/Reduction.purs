module Language.Lambda.Reduction where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Data.Traversable (class Traversable, traverse)
import Language.Lambda.Basis (class Basis, basisI, basisK, basisS)
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

class Reduction f var cat m where
  reduction :: cat (f (LambdaF var cat))
            -> m (f (LambdaF var cat))
 
reduce :: forall f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction f var cat m
         => Eq (f (LambdaF var cat))
         => Monad m
         => Traversable cat
         => f (LambdaF var cat) -> m (f (LambdaF var cat))
reduce = cataM reduceLambda

reduceLambda :: forall f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction f var cat m
         => Applicative m
         => AlgebraM m (LambdaF var cat) (f (LambdaF var cat))
reduceLambda =
  case _ of
    Var v -> pure $ var v
    Abs x e -> pure $ abs x e
    App a b -> composition a b
    Cat c -> reduction c

-- TODO extend to reduce to C and B combinators 
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
    Var v -> pure (var v)
--    App a b | isType b -> elimAbs a -- TODO let's do elimAbs over the Cofree typing of the lambda
                                       -- so we can ask isType of the type
    App a b -> app <$> elimAbs p a <*> elimAbs p b
    Abs x e ->
      case project e of
        Var v | v == x -> basisI p
        Abs _ f | x `freeIn` f -> abs x <$> elimAbs p e
        -- eta reduce
        App a b | b == var x -> elimAbs p a
        App a b | x `freeIn` e -> do
                s <- basisS p
                f <- app s <$> (elimAbs p (abs x a))
                app f <$> (elimAbs p (abs x b))

        Cat _ | x `freeIn` e -> abs x <$> elimAbs p e

        -- T[\x.E] => (K T[E]) (when x does not occur free in E) 
        _ -> do
           k <- basisK p
           app k <$> (elimAbs p e)
    Cat c -> cat <$> (traverse (elimAbs p) c)

