module Language.Lambda.Infer where

import Prelude

import Data.Traversable (class Traversable)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (LambdaF(..))
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (CoalgebraM)
import Matryoshka.Unfold (anaM)

class AbsRule :: Type -> Type -> Type -> ((Type -> Type) -> Type) -> (Type -> Type) -> Constraint
class AbsRule var exp typ f jujF | var -> typ where
  absRule :: var -> typ -> f jujF -> jujF exp

class AppRule :: forall k1 k2. k1 -> ((k1 -> k2) -> Type) -> (k1 -> k2) -> (k2 -> Type) -> Constraint
class AppRule exp f jujF m | exp -> f jujF where
  appRule :: f jujF -> f jujF -> m (jujF exp)
 
class VarRule :: Type -> Type -> Type -> (Type -> Type) -> Constraint
class VarRule var exp typ jujF | var -> typ where
  varRule :: var -> typ -> jujF exp

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
       => Rewrite typ m
       => TypingContext var typ m
       => AbsRule var exp typ f jujF
       => VarRule var exp typ jujF
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
      => Rewrite typ m
      => TypingContext var typ m
      => AbsRule var exp typ f jujF
      => VarRule var exp typ jujF
      => CoalgebraM m jujF exp
judge e =
  case project e of
    Abs b a -> do
       t <- fresh
       makeAssumption b t
       ja <- infer a
       t' <- applyCurrentSubstitution t
       pure $ absRule b t' ja 
    App f a -> join $ appRule <$> infer f <*> infer a
    Var v -> varRule v <$> (askEnvironment v >>= applyCurrentSubstitution)
    Cat c -> catRule c


----

class Supply :: Type -> (Type -> Type) -> Constraint
class Supply typ m where
  fresh :: m typ

class TypingContext var typ m | var -> typ where
  makeAssumption :: var -> typ -> m Unit
  askEnvironment :: var -> m typ

class Unify typ m where
  unify :: typ -> typ -> m typ
  unifyWithArrow :: typ -> m (typ /\ typ)

class TypingJudgement exp typ f jujF | exp -> typ where 
  judgement :: f jujF -> exp /\ typ

class TypingApplication exp typ jujF | exp -> typ where
  typingApplication :: exp -> exp -> typ -> jujF exp

class Substitution var typ m where
  substitute :: var -> typ -> m Unit

class Rewrite typ m where
  applyCurrentSubstitution :: typ -> m typ

instance
  ( Monad m
  , TypingJudgement exp typ f jujF
  , TypingApplication exp typ jujF
  , Rewrite typ m
  , Unify typ m
  ) => AppRule exp f jujF m where
  appRule f a = do
    let arrExp /\ arrTy = judgement f
    arrArg /\ arrRet <- unifyWithArrow arrTy
    let argExp /\ argTy = judgement a
    void $ unify argTy arrArg 
    appTy <- applyCurrentSubstitution arrRet
    pure $ typingApplication arrExp argExp appTy


