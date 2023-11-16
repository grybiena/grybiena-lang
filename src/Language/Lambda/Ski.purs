module Language.Lambda.Ski where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Data.Traversable (class Traversable, traverse)
import Language.Lambda.Calculus (LambdaF(..), abs, app, cat, freeIn, var)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)

-- TODO extend to reduce to C and B combinators 
elimAbs :: forall f var cat m.
          Recursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Ord var
       => Traversable cat
       => Functor cat
       => SKI cat m
       => Monad m
       => Eq (f (LambdaF var cat))
       => f (LambdaF var cat)
       -> m (f (LambdaF var cat))
elimAbs lam = 
  case project lam of
    Var v -> pure (var v)
    App a b -> app <$> elimAbs a <*> elimAbs b
    Abs x e ->
      case project e of
        Var v | v == x -> cat <$> skiI
        Abs _ f | x `freeIn` f -> (abs x <$> elimAbs e) >>= elimAbs  
        -- eta reduction
        App a b | b == var x -> elimAbs a
        App a b | x `freeIn` e -> do
                s <- cat <$> skiS
                f <- app s <$> (elimAbs (abs x a))
                app f <$> (elimAbs (abs x b))

        -- TODO Cat _ won't terminate under certain conditions... 
        -- e.g. \x -> prim x y
        -- may need specialized reduction for each prim...
        Cat _ | x `freeIn` e -> (abs x <$> elimAbs e) >>= elimAbs

        -- T[\x.E] => (K T[E]) (when x does not occur free in E) 
        _ -> do
           k <- cat <$> skiK
           app k <$> (elimAbs e)
    Cat c -> cat <$> (traverse elimAbs c)




class SKI cat m where
  skiS :: forall a. m (cat a) 
  skiK :: forall a. m (cat a)
  skiI :: forall a. m (cat a)



 
