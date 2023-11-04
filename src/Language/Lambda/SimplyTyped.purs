module Language.Lambda.SimplyTyped where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State (State, evalState, get, modify, modify_)
import Data.Either (Either)
import Data.Functor.Mu (Mu)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (maybe)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (LambdaF(..), abs, var)
import Language.Void.Value (VoidF(..), Value)
import Matryoshka.Algebra (AlgebraM, GAlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (CoalgebraM)
import Unsafe.Coerce (unsafeCoerce)


class Fresh ty m where
  fresh :: m ty

class FreshPat pat ty m where
  freshPat :: pat -> (ty -> m ty) -> m ty 

class BindEnv var ty m where
  bindVar :: var -> ty -> m Unit
  inferVar :: var -> m ty

class InferEnv var ty m where
  substitute :: var -> ty -> m Unit

class InferCat cat ty m where
  inferCat :: cat -> m ty

class Unify t m where
  unify :: t -> t -> m Unit

class InferErr var t m | m -> t, m -> var where
  funAppFailure :: forall a . t -> t -> m a
  notInScope :: forall a . var -> m a
  unificationError :: forall a . t -> t -> m a

class InferAbs pat typ m where
  inferAbs :: pat -> m typ -> m typ

class InferApp typ m where
  inferApp :: m typ -> m typ -> m typ

class InferCat' cat typ m where
  inferCat' :: cat (m typ) -> m typ

infer' :: forall pat var cat typ m.
          InferAbs pat typ m
       => InferApp typ m
       => BindEnv var typ m
       => InferCat' cat typ m
       => GAlgebraM m m (LambdaF pat var cat) typ 
infer' (Abs p e) = inferAbs p e
infer' (App f a) = inferApp f a
infer' (Var v) = inferVar v
infer' (Cat c) = inferCat' c

infer :: forall m var cat lam tvar tcat tlam .
         Monad m
      => Recursive lam (LambdaF var var cat)
      => Recursive tlam (LambdaF tlam tvar tcat) 
      => Corecursive tlam (LambdaF tlam tvar tcat)
      => Fresh tlam m
      => FreshPat var tlam m
      => InferEnv tvar tlam m
      => BindEnv var tlam m
      => InferCat (cat lam) tlam m
      => InferErr var tlam m
      => Unify tlam m
      => lam -> m tlam
infer lam =
  case project lam of
    Abs b a -> freshPat b $ \t -> abs <$> pure t <*> infer a
    App f a -> do
      tf <- infer f
      ta <- infer a
      case project tf of
        Abs ta' tb -> do
          unify ta ta'
          pure tb
        Var fa -> do
           x <- fresh
           y <- fresh
           substitute fa (abs x y)
           pure y
        _ -> funAppFailure tf ta
    Var v -> inferVar v
    Cat c -> inferCat c


newtype InferState tlam =
  InferState {
    nextVar :: Int
  , boundVars :: Map String tlam
  , substitutions :: Map String tlam
  }

data InferError tlam = FunAppFailure tlam tlam

type Infer t = ExceptT (InferError t) (State (InferState t))

instance 
  ( Corecursive tlam (LambdaF tlam String tcat)
  ) => Fresh tlam (Infer tlam) where
  fresh = do
   InferState { nextVar } <- modify (\(InferState st) ->
     InferState (st { nextVar = st.nextVar + 1 }))
   pure $ var ("t" <> show nextVar)


instance
  ( Corecursive tlam (LambdaF tlam String tcat)
  , InferErr String tlam (Infer tlam)
  ) => FreshPat String tlam (Infer tlam) where
  freshPat pat f = do
   t <- fresh
   InferState { boundVars } <- get
   bindVar pat t
   g <- f t
   modify_ (\(InferState st) -> InferState st { boundVars = boundVars })
   pure g

instance
  ( InferErr String tlam (Infer tlam)
  ) => BindEnv String tlam (Infer tlam) where
  bindVar var ty = do
     -- TODO warn of shadowing
     modify_ (\(InferState st) -> InferState (st { boundVars = Map.insert var ty st.boundVars })) 
  inferVar var = do
     InferState { boundVars } <- get
     maybe (notInScope var) pure (Map.lookup var boundVars )

instance
  ( InferErr String tlam (Infer tlam)
  ) => InferEnv String tlam (Infer tlam) where
  substitute var ty = do
     -- TODO check existing binding is subsumed by new binding if exists
     modify_ (\(InferState st) -> InferState (st { substitutions = Map.insert var ty st.substitutions })) 

instance InferCat (VoidF lam) tlam m where
  inferCat (VoidF v) = absurd v

instance
  ( Recursive tlam (LambdaF tlam String tcat)
  , InferEnv String tlam m
  , InferErr String tlam m
  , Monad m
  ) => Unify tlam m where
  unify ta tb = do
     case project ta /\ project tb of
       Var a /\ Var b | a == b -> pure unit
       Var a /\ _ -> substitute a tb
       _ /\ Var b -> substitute b ta
       Abs ab aa /\ Abs bb ba -> do
          unify ab bb
          unify aa ba
       App ab aa /\ App bb ba -> do
          unify ab bb
          unify aa ba
       _ -> unificationError ta tb

newtype TypeF t = TypeF (LambdaF t String VoidF t)
type Type' = Mu TypeF


