module Language.Void.Type where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Except.Trans (class MonadThrow)
import Control.Monad.State (class MonadState, StateT, evalState, get, gets, modify_)
import Data.Either (Either)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (class PrettyLambda, Lambda, LambdaF(..), prettyVar)
import Language.Lambda.Infer (class AppRule, class CatRule, class Supply, class TypingAbstraction, class TypingContext, class TypingRelation, infer)
import Language.Void.Value (Value, VoidF(..))
import Matryoshka.Class.Recursive (class Recursive, project)
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
instance Eq (TT a) where
  eq  _ _ = true

type Type' = Lambda String TT

instance PrettyLambda String TT where
  prettyAbs i a = text "forall" <+> (prettyVar i <> text ".") <+> pretty a
  prettyApp (In (App (In (Cat Arrow)) a)) b = pretty a <+> text "->" <+> pretty b
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat Arrow = text "->"
 

newtype UnificationState =
  UnificationState {
    nextVar :: Int
  , typingAssumptions :: Map String Type'
  }

data UnificationError =
    NotInScope String
  | Err String
  | InvalidApp Type' Value
  | UnificationError Type' Type' 

derive instance Generic UnificationError _
instance Show UnificationError where
  show = genericShow

newtype UnifyT m a = UnifyT (ExceptT UnificationError (StateT UnificationState m) a)
derive newtype instance Functor m => Functor (UnifyT m)
derive newtype instance Monad m => Apply (UnifyT m)
derive newtype instance Monad m => Applicative (UnifyT m)
derive newtype instance Monad m => Bind (UnifyT m)
derive newtype instance Monad m => Monad (UnifyT m)
derive newtype instance Monad m => MonadState UnificationState (UnifyT m)
derive newtype instance Monad m => MonadThrow UnificationError (UnifyT m)

data JudgementF var typ a =
    HasType var typ
  | JudgeApp a a typ
  | JudgeAbs var a typ

type Judgement = Mu (JudgementF String Type')

data Typing exp typ = Typing exp typ

instance TypingRelation var exp typ (JudgementF var typ) where
  typingRelation = HasType

instance TypingAbstraction String Value Type' Mu (JudgementF String Type') where
  typingAbstraction b t j =
    let Typing e ret = assume j
      in JudgeAbs b e (In (App (In (App (In (Cat Arrow)) t)) ret)) 


class Assumption juj exp typ | juj -> exp, juj -> typ where
  assume :: juj -> Typing exp typ


instance Assumption Judgement Value Type' where
  assume (In (HasType e t)) = Typing (In (Var e)) t
  assume (In (JudgeApp a b t)) = 
    let Typing e1 _ = assume a
        Typing e2 _ = assume b
     in Typing (In (App e1 e2)) t
  assume (In (JudgeAbs a b t)) =
    let Typing e2 _ = assume b
     in Typing (In (Abs a e2)) t


instance Functor (JudgementF exp typ) where
  map _ (HasType e i) = HasType e i
  map f (JudgeApp a b t) = JudgeApp (f a) (f b) t
  map f (JudgeAbs a b t) = JudgeAbs a (f b) t

instance Foldable (JudgementF exp typ) where
  foldr _ b (HasType _ _) = b
  foldr f b (JudgeApp x y _) = f y (f x b) 
  foldr f b (JudgeAbs _ y _) = f y b
  foldl _ b (HasType _ _) = b
  foldl f b (JudgeApp x y _) = f (f b y) x
  foldl f b (JudgeAbs _ y _) = f b y
  foldMap _ (HasType _ _) = mempty
  foldMap f (JudgeApp x y _) = f x <> f y
  foldMap f (JudgeAbs _ y _) = f y

instance Traversable (JudgementF exp typ) where
  traverse _ (HasType e t) = pure $ HasType e t
  traverse f (JudgeApp a b t) = (\ta tb -> JudgeApp ta tb t) <$> f a <*> f b
  traverse f (JudgeAbs a b t) = (\tb -> JudgeAbs a tb t) <$> f b
  sequence = traverse identity

runInfer :: Value -> Either UnificationError Type'
runInfer v = foo <$> runUnifyT (infer v)
  where
    foo :: Judgement -> Type'
    foo j = let Typing _ t = assume j in t

runUnifyT :: forall a . UnifyT Identity a -> Either UnificationError a
runUnifyT (UnifyT f) =  evalState (runExceptT f) (UnificationState { nextVar: 0, typingAssumptions: Map.empty })


instance Monad m => Supply Type' (UnifyT m) where
  fresh = do
    nextVar <- gets (\(UnificationState st) -> st.nextVar)
    let t = In (Var ("t" <> show nextVar))
    modify_ (\(UnificationState st) -> UnificationState st {
                  nextVar = st.nextVar + 1
                })
    pure t

instance Monad m => TypingContext String Type' (UnifyT m) where
  makeAssumption v t =
     modify_ (\(UnificationState st) -> UnificationState st {
       typingAssumptions = Map.insert v t st.typingAssumptions
       })
  askEnvironment v = do
    UnificationState st <- get
    case Map.lookup v st.typingAssumptions of
      Just t -> pure t
      Nothing -> throwError $ NotInScope v


instance Monad m => Unification Type' String (UnifyT m) where
  substitute _ _ = pure unit
  lookupTermVariableAssumption v = do
     UnificationState st <- get
     case Map.lookup v st.typingAssumptions of
       Just t -> pure t
       Nothing -> throwError $ NotInScope v
  unificationError t1 t2 = throwError $ UnificationError t1 t2

-----------------------------



instance
  ( Monad m
  , Assumption Judgement Value Type' 
  , Unification Type' String (UnifyT m)
  ) => AppRule Value Mu (JudgementF String Type') (UnifyT m) where
  appRule j1 j2 = do
     let (Typing e1 t1) = assume j1
         (Typing e2 t2) = assume j2
     case t1 of
       (In (App (In (App (In (Cat Arrow)) a)) b)) -> do
          unify a t2
          pure $ JudgeApp e1 e2 b
       _ -> throwError $ InvalidApp t1 e2 

instance Monad m => CatRule VoidF Value (JudgementF String Type') m where 
  catRule (VoidF v) = absurd v



---- Language.Lambda.Unify

class Unification typ var m | typ -> var where
  substitute :: var -> typ -> m Unit
  lookupTermVariableAssumption :: var -> m typ
--  applyCurrentSubstitution :: typ -> m typ
  unificationError :: forall a . typ -> typ -> m a



unify :: forall typ var cat m.
         Recursive typ (LambdaF var cat)
      => Eq var
      => Eq (cat typ)
      => Monad m
      => Unification typ var m
      => typ -> typ -> m Unit
unify ta tb = do
   case project ta /\ project tb of
     Var a /\ Var b | a == b -> pure unit
     Var a /\ _ -> substitute a tb
     _ /\ Var b -> substitute b ta
     Abs ab aa /\ Abs bb ba -> do
--        unify ab bb
        unify aa ba
     App ab aa /\ App bb ba -> do
        unify ab bb
        unify aa ba
     Cat ca /\ Cat cb | ca == cb -> pure unit
     _ -> unificationError ta tb


