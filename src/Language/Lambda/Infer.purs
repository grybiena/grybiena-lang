module Language.Lambda.Infer where

import Prelude

import Control.Monad.Writer (class MonadTell, tell)
import Data.Traversable (class Traversable)
import Language.Lambda.Calculus (LambdaF(..))
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (CoalgebraM)
import Matryoshka.Unfold (anaM)

-- | A Typing assumption of the form `x:t" meaning _x_ has type _t_
data Typing x t = Typing x t

class BindPat :: Type -> Type -> (Type -> Type) -> Constraint
class BindPat var typ m where
  bindPat :: var -> m (Typing var typ)

class AbsRule :: Type -> Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class AbsRule var exp typ juj m | exp -> typ where
  absRule :: Typing var typ -> Typing exp typ -> m (juj exp)

class AppRule :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class AppRule exp typ juj m | exp -> typ where
  appRule :: Typing exp typ -> Typing exp typ -> m (juj exp)
 
class VarRule :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class VarRule var exp juj m where
  varRule :: var -> m (juj exp)

class CatRule :: (Type -> Type) -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class CatRule cat exp juj m where
  catRule :: cat exp -> m (juj exp)

infer :: forall typ juj m exp var cat.
          Corecursive typ juj
       => Monad m
       => Traversable juj
       => Recursive exp (LambdaF var cat)
       => BindPat var typ m
       => AbsRule var exp typ juj m
       => AppRule exp typ juj m
       => VarRule var exp juj m
       => CatRule cat exp juj m
       => MonadTell (juj exp) m
       => exp -> m (Typing exp typ)
infer exp = Typing exp <$> anaM go exp 
  where
    ju j = tell j *> pure j
    go :: CoalgebraM m juj exp
    go e = ju =<< case project e of
      Abs b a -> join $ absRule <$> bindPat b <*> infer a
      App f a -> join $ appRule <$> infer f <*> infer a
      Var v -> varRule v
      Cat c -> catRule c
 
