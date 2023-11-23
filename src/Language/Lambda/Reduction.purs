module Language.Lambda.Reduction where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Control.Comonad.Cofree (Cofree, head, mkCofree, tail, (:<))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import Language.Lambda.Calculus (class Shadow, LambdaF(..), abs, app, cat, freeIn, var)
import Language.Lambda.Inference (class Arrow, class Inference, class IsType, arrow, flat, infer, isType, unifyWithArrow)
import Language.Lambda.Unification (class Context, class Fresh, class Substitute, class Unify, rewrite, unify)
import Matryoshka.Algebra (AlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cataM)

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
elimAbs :: forall f var cat m.
          Recursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Ord var
       => Traversable cat
       => Functor cat
       => Basis cat (f (LambdaF var cat)) m
       => Monad m
       => IsType (f (LambdaF var cat))
       => Eq (f (LambdaF var cat))
       => f (LambdaF var cat)
       -> m (f (LambdaF var cat))
elimAbs lam = 
  case project lam of
    Var v -> pure (var v)
--    App a b | isType b -> elimAbs a -- TODO let's do elimAbs over the Cofree typing of the lambda
                                       -- so we can ask isType of the type
    App a b -> app <$> elimAbs a <*> elimAbs b
    Abs x e ->
      case project e of
        Var v | v == x -> cat <$> basisI
        Abs _ f | x `freeIn` f -> abs x <$> elimAbs e
        -- eta reduce
        App a b | b == var x -> elimAbs a
        App a b | x `freeIn` e -> do
                s <- cat <$> basisS
                f <- app s <$> (elimAbs (abs x a))
                app f <$> (elimAbs (abs x b))

        Cat _ | x `freeIn` e -> abs x <$> elimAbs e

        -- T[\x.E] => (K T[E]) (when x does not occur free in E) 
        _ -> do
           k <- cat <$> basisK
           app k <$> (elimAbs e)
    Cat c -> pure $ cat c
--    Cat c -> cat <$> (traverse elimAbs c)
 -- TODO this is hmmmm...
  --   -- do we want to elimAbs on the nativeType????
        -- e.g. ((forall a. a -> a)
        -- then we get the SK basis appearing in the types... 
        -- like "(forall a . (a -> (Effect a)))" can be writ as "((S ->) Effect)"
        -- since S :: forall a b c . (a -> b -> c) -> (a -> b) -> a -> c 
        --       (->) :: * -> * -> *
        --       Effect :: * -> *
        -- ------------------------------ 
        --       ((S ->) Effect) :: * -> *
        --
        -- which seems morally correct but also strange
        -- to support this we need to be able to unify the two representations which we don't support yet...
        -- 
        -- 
        -- the downside is without this we don't elimAbs any values embedded in the category
        -- which gives a lot of weight to the moral argument






class Basis :: forall k1 k2. (k1 -> k2) -> k1 -> (k2 -> Type) -> Constraint
class Basis cat term m where
  basisS :: m (cat term) 
  basisK :: m (cat term)
  basisI :: m (cat term)



-- TODO extend to reduce to C and B combinators 
elimAbs' :: forall f var cat m.
          Recursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Ord var
       => Traversable cat
       => Functor cat
       => Basis cat (f (LambdaF var cat)) m
       => Fresh (f (LambdaF var cat)) m 
       => Arrow (f (LambdaF var cat)) 
       => Shadow var
       => Unify (f (LambdaF var cat)) (f (LambdaF var cat)) m 
       => Inference var cat (f (LambdaF var cat)) m 
       => Context var (f (LambdaF var cat)) m 
       => Substitute var cat f m
       => Monad m
       => IsType (f (LambdaF var cat))
       => Eq (f (LambdaF var cat))
       => MonadEffect m
       => Show (f (LambdaF var cat))
       => (Cofree (LambdaF var cat) (f (LambdaF var cat)))
       -> m (Cofree (LambdaF var cat) (f (LambdaF var cat)))
elimAbs' lam = 
  case tail lam of
    Var v -> pure (head lam :< Var v)
    App a b -> do
      (\z q -> head lam :< App z q) <$> elimAbs' a <*> elimAbs' b
    Abs x e ->
      case tail e of
        Var v | v == x -> do
          (i :: f (LambdaF var cat)) <- cat <$> basisI
          infer i
        Abs _ f | x `freeIn` flat f -> (mkCofree (head lam) <<< Abs x) <$> elimAbs' e
        -- eta reduce
        App a b | eta b x -> elimAbs' a
        App a b | x `freeIn` flat e -> do
                (s' :: f (LambdaF var cat)) <- cat <$> basisS
                s <- infer s'
                arrArg /\ _ <- unifyWithArrow (head lam)
                let arr = arrow arrArg (head a)
                f <- (\q -> app (head s) arr :< App s q) <$> (elimAbs' (arr :< Abs x a))
                (\q -> head lam :< App f q)  <$> (elimAbs' (arrow arrArg (head b) :< Abs x b))

        Cat _ | x `freeIn` flat e -> (\q -> head lam :< Abs x q) <$> elimAbs' e

        -- T[\x.E] => (K T[E]) (when x does not occur free in E) 
        _ -> do
           (k' :: f (LambdaF var cat)) <- cat <$> basisK
           k <- infer k'
           (\q -> head lam :< App k q)  <$> (elimAbs' e)

    Cat c ->  (\k -> head lam :< Cat k) <$> (traverse elimAbs' c)
  where
    eta b x =
      case tail b of
        Var x' -> x == x'
        _ -> false

 
