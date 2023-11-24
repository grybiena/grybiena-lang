module Language.Lambda.Reduction where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState)
import Data.Foldable (class Foldable)
import Data.Homogeneous.Record (fromHomogeneous)
import Data.Traversable (class Traversable, traverse)
import Language.Kernel.Basis (basis)
import Language.Lambda.Calculus (class Shadow, LambdaF(..), abs, app, cat, freeIn, var)
import Language.Lambda.Inference (class IsType)
import Language.Lambda.Unification (class Fresh, TypingContext)
import Language.Native (class NativeValue, native)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Class (class StringParserT, class TypeParser)
import Matryoshka.Algebra (AlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cataM)
import Parsing (ParseError)
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


class (Monad (t m), Monad m) <= Basis t m f var cat where
  basisS :: Proxy t -> m (f (LambdaF var cat)) 
  basisK :: Proxy t -> m (f (LambdaF var cat)) 
  basisI :: Proxy t -> m (f (LambdaF var cat)) 

instance
  ( MonadRec m
  , MonadThrow ParseError m
  , MonadState (TypingContext var f var cat) m
  , NativeValue f var cat
  , Fresh var m
  , Ord var
  , Shadow var
  , Foldable cat
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , TypeParser t m f var cat
  , StringParserT t m
  ) => Basis t m f var cat where
  basisS p = native <$> (fromHomogeneous (unsafeModule p basis))."S"
  basisK p = native <$> (fromHomogeneous (unsafeModule p basis))."K"
  basisI p = native <$> (fromHomogeneous (unsafeModule p basis))."I"



