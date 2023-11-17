module Language.Lambda.Reduction where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (LambdaF(..), abs, app, cat, freeIn, var)
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata)

class Composition f var cat where 
  composition :: f (LambdaF var cat)
          -> f (LambdaF var cat)
          -> f (LambdaF var cat)
 
reduce :: forall f var cat.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat
         => Eq (f (LambdaF var cat))
         => f (LambdaF var cat) -> f (LambdaF var cat)
reduce = cata reduction

reduction :: forall f var cat.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat
         => Algebra (LambdaF var cat) (f (LambdaF var cat))
reduction =
  case _ of
    Var v -> var v
    Abs x e -> abs x e
    App a b -> composition a b
    Cat c -> cat c

-- TODO extend to reduce to C and B combinators 
elimAbs :: forall f var cat m.
          Recursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Ord var
       => Traversable cat
       => Functor cat
       => Basis cat m
       => Monad m
       => Composition f var cat
       => Eq (f (LambdaF var cat))
       => f (LambdaF var cat)
       -> m (f (LambdaF var cat))
elimAbs lam = 
  case project lam of
    Var v -> pure (var v)
    -- TODO reduce (App (Cat _) (Cat _))
    App a b -> app <$> elimAbs a <*> elimAbs b
    Abs x e ->
      case project e of
        Var v | v == x -> cat <$> basisI
        Abs _ f | x `freeIn` f -> (abs x <$> elimAbs e) >>= elimAbs  
        -- eta reduction
        App a b | b == var x -> elimAbs a
        App a b | x `freeIn` e -> do
                s <- cat <$> basisS
                f <- app s <$> (elimAbs (abs x a))
                app f <$> (elimAbs (abs x b))

        Cat _ | x `freeIn` e -> (abs x <$> elimAbs e) >>= elimAbs

        -- T[\x.E] => (K T[E]) (when x does not occur free in E) 
        _ -> do
           k <- cat <$> basisK
           app k <$> (elimAbs e)
    Cat c -> cat <$> (traverse elimAbs c)




class Basis :: forall k1 k2. (k1 -> k2) -> (k2 -> Type) -> Constraint
class Basis cat m where
  basisS :: forall a. m (cat a) 
  basisK :: forall a. m (cat a)
  basisI :: forall a. m (cat a)



 
