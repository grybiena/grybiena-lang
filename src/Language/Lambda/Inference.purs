module Language.Lambda.Inference where

import Prelude

import Control.Comonad.Cofree (Cofree, head, (:<))
import Data.Foldable (class Foldable)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (class Context, LambdaF(..), rewrite)
import Language.Void.Value (VoidF(..))
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive)
import Matryoshka.Fold (cata)

infer :: forall exp var cat m typ .
        Monad m
     => Recursive exp (LambdaF var cat)
     => Supply typ m
     => TypingContext var typ m
     => Rewrite typ m
     => Unify typ m
     => Arrow typ
     => CatRule var cat typ m
     => exp -> (m (Cofree (LambdaF var cat) typ)) 
infer = cata rule

rule :: forall var cat m typ .
        Monad m
     => Supply typ m
     => TypingContext var typ m
     => Rewrite typ m
     => Unify typ m
     => Arrow typ
     => CatRule var cat typ m
     => Algebra (LambdaF var cat) (m (Cofree (LambdaF var cat) typ)) 
rule expr = 
  case expr of
    Abs b a -> absRule b a  
    App f a -> join $ appRule <$> f <*> a
    Var v -> askEnvironment v >>= \t -> pure (t :< Var v)
    Cat c -> catRule c


class CatRule var cat typ m where
  catRule :: cat (m (Cofree (LambdaF var cat) typ)) -> m (Cofree (LambdaF var cat) typ)

instance CatRule var VoidF typ m where 
  catRule (VoidF v) = absurd v

absRule :: forall m typ var cat.
           Bind m
        => Supply typ m
        => TypingContext var typ m
        => Rewrite typ m
        => Arrow typ
        => Applicative m
        => var
        -> m (Cofree (LambdaF var cat) typ)
        -> m (Cofree (LambdaF var cat) typ)
absRule binding inferBody = do 
  tyBind <- fresh
  makeAssumption binding tyBind
  tyBody <- inferBody
  tyBind' <- applyCurrentSubstitution tyBind 
  pure $ (arrow tyBind' (head tyBody)) :< (Abs binding tyBody)


appRule :: forall m typ var cat.
           Bind m
        => Unify typ m
        => Applicative m
        => Cofree (LambdaF var cat) typ
        -> Cofree (LambdaF var cat) typ
        -> m (Cofree (LambdaF var cat) typ)
appRule f a = do
  let arrTy = head f
  arrArg /\ arrRet <- unifyWithArrow arrTy
  let argTy = head a
  void $ unify arrArg argTy
  pure $ arrRet :< (App f a)



----

class Arrow typ where
  arrow :: typ -> typ -> typ

class TypingContext var typ m | var -> typ where
  makeAssumption :: var -> typ -> m Unit
  askEnvironment :: var -> m typ

class Supply :: Type -> (Type -> Type) -> Constraint
class Supply typ m where
  fresh :: m typ

class Rewrite typ m where
  applyCurrentSubstitution :: typ -> m typ

class Unify typ m where
  unify :: typ -> typ -> m typ
  unifyWithArrow :: typ -> m (typ /\ typ)


instance
  ( Context var cat f m
  , Foldable cat
  , Functor m
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , Eq var
  ) => Rewrite (f (LambdaF var cat)) m where
  applyCurrentSubstitution = rewrite


