module Language.Lambda.Infer where

import Prelude

import Data.Traversable (class Traversable)
import Language.Lambda.Calculus (LambdaF(..))
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (CoalgebraM)
import Matryoshka.Unfold (anaM)

class AppRule :: forall k1 k2. k1 -> ((k1 -> k2) -> Type) -> (k1 -> k2) -> (k2 -> Type) -> Constraint
class AppRule exp f jujF m | exp -> f jujF where
  appRule :: f jujF -> f jujF -> m (jujF exp)
 
class CatRule :: forall k1 k2. (k1 -> Type) -> k1 -> (k1 -> k2) -> (k2 -> Type) -> Constraint
class CatRule cat exp jujF m where
  catRule :: cat exp -> m (jujF exp)

infer :: forall f jujF m exp var cat typ.
          Corecursive (f jujF) jujF
       => Monad m
       => Traversable jujF
       => Recursive exp (LambdaF var cat)
       => AppRule exp f jujF m
       => CatRule cat exp jujF m
       => Supply typ m
       => TypingContext var typ m
       => TypingAbstraction var exp typ f jujF
       => TypingRelation var exp typ jujF
       => exp -> m (f jujF)
infer exp = anaM judge exp 

judge :: forall f jujF m exp var cat typ.
         Corecursive (f jujF) jujF
      => Monad m
      => Traversable jujF
      => Recursive exp (LambdaF var cat)
      => AppRule exp f jujF m
      => CatRule cat exp jujF m
      => Supply typ m
      => TypingContext var typ m
      => TypingAbstraction var exp typ f jujF
      => TypingRelation var exp typ jujF
      => CoalgebraM m jujF exp
judge e =
  case project e of
    Abs b a -> do
       t <- fresh
       makeAssumption b t
       typingAbstraction b t <$> infer a
    App f a -> join $ appRule <$> infer f <*> infer a
    Var v -> typingRelation v <$> askEnvironment v
    Cat c -> catRule c


----

class Supply :: Type -> (Type -> Type) -> Constraint
class Supply typ m where
  fresh :: m typ

class TypingContext var typ m | var -> typ where
  makeAssumption :: var -> typ -> m Unit
  askEnvironment :: var -> m typ

class TypingRelation :: Type -> Type -> Type -> (Type -> Type) -> Constraint
class TypingRelation var exp typ jujF | var -> typ where
  typingRelation :: var -> typ -> jujF exp

class TypingAbstraction :: Type -> Type -> Type -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
class TypingAbstraction var exp typ f jujF | var -> typ where
  typingAbstraction :: var -> typ -> f jujF -> jujF exp

