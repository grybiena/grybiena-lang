module Language.Void.Type where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State (StateT, evalState, get, gets, modify_)
import Data.Either (Either)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Language.Lambda.Calculus (class PrettyLambda, Lambda, LambdaF(..), prettyVar)
import Language.Lambda.Infer (class AppRule, class CatRule, class VarRule, Typing(..))
import Language.Void.Value (Value, VoidF(..))
import Prettier.Printer (text, (<+>))
import Pretty.Printer (pretty)

data TT :: forall k. k -> Type
data TT a =
  Arrow 

--instance ArrowType (TT a) where
--  arrowType = Arrow

derive instance Generic (TT a) _
instance Show (TT a) where
  show = genericShow
instance Functor TT where
  map _ Arrow = Arrow


type Type' = Lambda String TT

instance PrettyLambda String TT where
  prettyAbs i a = text "forall" <+> (prettyVar i <> text ".") <+> pretty a
  prettyApp (In (App (In (Cat Arrow)) a)) b = pretty a <+> text "->" <+> pretty b
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat Arrow = text "->"
 

newtype UnificationState =
  UnificationState {
    nextVar :: Int
  , currentSubstitution :: Map String (Judgement Value Type' Value)
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

data Judgement exp typ a =
    HasType exp typ
  | JudgeApp a a typ


instance Functor (Judgement exp typ) where
  map _ (HasType e i) = HasType e i
  map f (JudgeApp a b t) = JudgeApp (f a) (f b) t

instance Foldable (Judgement exp typ) where
  foldr _ b (HasType _ _) = b
  foldr f b (JudgeApp x y _) = f y (f x b) 
  foldl _ b (HasType _ _) = b
  foldl f b (JudgeApp x y _) = f (f b y) x
  foldMap _ (HasType _ _) = mempty
  foldMap f (JudgeApp x y _) = f x <> f y

instance Traversable (Judgement exp typ) where
  traverse _ (HasType e t) = pure $ HasType e t
  traverse f (JudgeApp a b t) = (\ta tb -> JudgeApp ta tb t) <$> f a <*> f b
  sequence = traverse identity


---- -- this is an Orphan instance but we can extract the type from the judgement like this
----instance Corecursive typ (Judgement ex typ) where
----  embed (HasType _ t) = t
----  embed (JudgeApp _ _ t) = t 

--runInfer :: Value -> Either UnificationError Type'
--runInfer v = evalState (runExceptT (infer v)) (UnificationState { nextVar: 0, currentSubstitution: Map.empty })
--
--instance Monad m => InferPat String String TT (UnifyT m) where 
--  withFresh v f = do
--    nextVar <- gets (\(UnificationState st) -> st.nextVar)
--    let t = In (Var ("t" <> show nextVar))
--    modify_ (\(UnificationState st) -> UnificationState st {
--                  nextVar = st.nextVar + 1, currentSubstitution = Map.insert v t st.currentSubstitution
--                })
--    f t

instance Monad m => AppRule Value Type' (Judgement Value Type') (UnifyT m) where
  appRule (Typing e1 t1) (Typing e2 t2) = do
     case t1 of
       (In (App (In (App (In (Cat Arrow)) a)) b)) -> do
--          unify a t2
          pure $ JudgeApp e1 e2 b
       _ -> throwError $ InvalidApp t1 e2 


instance Monad m => VarRule String Value (Judgement Value Type') (UnifyT m) where 
  varRule v = do
    UnificationState st <- get
    case Map.lookup v st.currentSubstitution of
      Just t -> pure t
      Nothing -> throwError $ NotInScope v

instance Monad m => CatRule VoidF Value (Judgement Value Type') m where 
  catRule (VoidF v) = absurd v

--instance Monad m => Unification String TT (UnifyT m) where 
--  fresh = do
--    nextVar <- gets (\(UnificationState st) -> st.nextVar)
--    let t = In (Var ("t" <> show nextVar))
--    modify_ (\(UnificationState st) -> UnificationState st { nextVar = st.nextVar + 1 })
--    pure t
--  applyCurrentSubstitution = pure --TODO
--  replaceVarWithFresh _ = pure --TODO
--  substitute s t = do
--     modify_ (\(UnificationState st) -> UnificationState st { currentSubstitution = Map.insert s t st.currentSubstitution })
--  unificationError t = throwError <<< UnificationError t
--  skolemize _ = pure
--


--  unify ta tb = do
--     case project ta /\ project tb of
--       Var a /\ Var b | a == b -> pure unit
--       Var a /\ _ -> substitute a tb
--       _ /\ Var b -> substitute b ta
--       Abs ab aa /\ Abs bb ba -> do
--          unify ab bb
--          unify aa ba
--       App ab aa /\ App bb ba -> do
--          unify ab bb
--          unify aa ba
--       _ -> unificationError ta tb


