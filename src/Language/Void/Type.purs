module Language.Void.Type where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State (StateT, evalState, get, gets, modify_)
import Data.Either (Either)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Language.Lambda.Calculus (class PrettyLambda, Lambda, LambdaF(..), prettyVar)
import Language.Lambda.Inference (class ArrowType, class InferCat, class InferPat, class InferVar, class Unification, infer, invalidApp)
import Language.Void.Value (Value, VoidF(..))
import Prettier.Printer (text, (<+>))
import Pretty.Printer (pretty)

data TT :: forall k. k -> Type
data TT a =
  Arrow 

instance ArrowType (TT a) where
  arrowType = Arrow

derive instance Generic (TT a) _
instance Show (TT a) where
  show = genericShow
instance Functor TT where
  map _ Arrow = Arrow


type Type' = Lambda String String TT

instance PrettyLambda String String TT where
  prettyAbs i a = text "forall" <+> (prettyVar i <> text ".") <+> pretty a
  prettyApp (In (App (In (Cat Arrow)) a)) b = pretty a <+> text "->" <+> pretty b
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat Arrow = text "->"
 

newtype UnificationState =
  UnificationState {
    nextVar :: Int
  , currentSubstitution :: Map String Type'
  }

data UnificationError =
    NotInScope String
  | Err String
  | InvalidApp Type' Value
  | UnificationError Type' Type' 

derive instance Generic UnificationError _
instance Show UnificationError where
  show = genericShow

type UnifyT m = ExceptT UnificationError (StateT UnificationState m)

runInfer :: Value -> Either UnificationError Type'
runInfer v = evalState (runExceptT (infer v)) (UnificationState { nextVar: 0, currentSubstitution: Map.empty })

instance Monad m => InferPat String String TT (UnifyT m) where 
  withFresh v f = do
    nextVar <- gets (\(UnificationState st) -> st.nextVar)
    let t = In (Var ("t" <> show nextVar))
    modify_ (\(UnificationState st) -> UnificationState st {
                  nextVar = st.nextVar + 1, currentSubstitution = Map.insert v t st.currentSubstitution
                })
    f t

instance Monad m => InferVar String String TT (UnifyT m) where 
  inferVar v = do
    UnificationState st <- get
    case Map.lookup v st.currentSubstitution of
      Just t -> pure t
      Nothing -> throwError $ NotInScope v

instance Monad m => InferCat String String VoidF String TT (UnifyT m) where 
  inferCat (VoidF v) = absurd v
  inferCatApp i v = invalidApp (In (Cat i)) v
  invalidApp i v = throwError $ InvalidApp i v

instance Monad m => Unification String TT (UnifyT m) where 
  fresh = do
    nextVar <- gets (\(UnificationState st) -> st.nextVar)
    let t = In (Var ("t" <> show nextVar))
    modify_ (\(UnificationState st) -> UnificationState st { nextVar = st.nextVar + 1 })
    pure t
  applyCurrentSubstitution = pure --TODO
  replaceVarWithFresh _ = pure --TODO
  substitute s t = do
     modify_ (\(UnificationState st) -> UnificationState st { currentSubstitution = Map.insert s t st.currentSubstitution })
  unificationError t = throwError <<< UnificationError t
  skolemize _ = pure

