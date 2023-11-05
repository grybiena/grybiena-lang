module Language.Lambda.Infer where

import Prelude

import Data.Traversable (class Traversable)
import Language.Lambda.Calculus (LambdaF(..))
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (CoalgebraM)
import Matryoshka.Unfold (anaM)

class BindRule var m where
  bindRule :: var -> m Unit

class AbsRule :: Type -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class AbsRule var exp juj jujF m | exp -> juj where
  absRule :: var -> juj -> m (jujF exp)

class AppRule :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class AppRule exp juj jujF m | exp -> juj where
  appRule :: juj -> juj -> m (jujF exp)
 
class VarRule :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class VarRule var exp jujF m where
  varRule :: var -> m (jujF exp)

class CatRule :: (Type -> Type) -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class CatRule cat exp jujF m where
  catRule :: cat exp -> m (jujF exp)

infer :: forall juj jujF m exp var cat.
          Corecursive juj jujF
       => Monad m
       => Traversable jujF
       => Recursive exp (LambdaF var cat)
       => BindRule var m
       => AbsRule var exp juj jujF m
       => AppRule exp juj jujF m
       => VarRule var exp jujF m
       => CatRule cat exp jujF m
       => exp -> m juj
infer exp = anaM judge exp 

judge :: forall juj jujF m exp var cat.
         Corecursive juj jujF
      => Monad m
      => Traversable jujF
      => Recursive exp (LambdaF var cat)
      => BindRule var m
      => AbsRule var exp juj jujF m
      => AppRule exp juj jujF m
      => VarRule var exp jujF m
      => CatRule cat exp jujF m
      => CoalgebraM m jujF exp
judge e =
  case project e of
    Abs b a -> bindRule b *> join (absRule b <$> infer a)
    App f a -> join $ appRule <$> infer f <*> infer a
    Var v -> varRule v
    Cat c -> catRule c


----

class Supply :: Type -> (Type -> Type) -> Constraint
class Supply typ m where
  fresh :: m typ

class TypingContext var typ m | var -> typ where
  makeAssumption :: var -> typ -> m Unit
  askEnvironment :: var -> m typ

instance
  ( Monad m
  , Supply typ m
  , TypingContext var typ m
  ) => BindRule var m where
  bindRule v = fresh >>= makeAssumption v

class TypingRelation :: Type -> Type -> Type -> (Type -> Type) -> Constraint
class TypingRelation var exp typ jujF | var -> typ where
  typingRelation :: var -> typ -> jujF exp

instance
  ( Monad m
  , TypingContext var typ m
  , TypingRelation var exp typ jujF
  ) => VarRule var exp jujF m where 
  varRule v = typingRelation v <$> askEnvironment v


class TypingAbstraction var exp typ juj jujF | var -> typ where
  typingAbstraction :: var -> typ -> juj -> jujF exp

instance
  ( Monad m
  , TypingContext var typ m
  , TypingAbstraction var exp typ juj jujF
  ) => AbsRule var exp juj jujF m where
  absRule b j = typingAbstraction b <$> askEnvironment b <*> pure j




