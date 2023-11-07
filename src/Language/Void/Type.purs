module Language.Void.Type where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Except.Trans (class MonadThrow)
import Control.Monad.State (class MonadState, StateT, get, gets, modify_, runState)
import Data.Either (Either)
import Data.Eq (class Eq1)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, Lambda, LambdaF(..), abs, absMany, app, cat, prettyVar, var)
import Language.Lambda.Infer (class AbsRule, class Rewrite, class Substitution, class Supply, class TypingApplication, class TypingContext, class TypingJudgement, class Unify, class VarRule, applyCurrentSubstitution, fresh, infer, judgement, substitute, unify)
import Language.Parser.Common (buildPostfixParser, identifier, parens, reservedOp)
import Language.Void.Value (ValVar, Value)
import Matryoshka.Class.Recursive (project)
import Parsing (ParserT)
import Parsing.Combinators (many1Till)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (pretty)

data TT :: forall k. k -> Type
data TT a =
  Arrow 

derive instance Generic (TT a) _
instance Show (TT a) where
  show = genericShow
instance Functor TT where
  map _ Arrow = Arrow
instance Eq (TT a) where
  eq  _ _ = true
instance Eq1 TT where
  eq1  _ _ = true



type Type' = Lambda TyVar TT

instance PrettyVar TyVar where
  prettyVar (TyVar v) = text v

instance PrettyLambda TyVar TT where
  prettyAbs i a = text "forall" <+> (prettyVar i <> text ".") <+> pretty a
  prettyApp (In (App (In (Cat Arrow)) a)) b = text "(" <> pretty a <+> text "->" <+> pretty b <> text ")"
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat Arrow = text "->"
 
newtype TyVar = TyVar String
derive newtype instance Show TyVar
derive newtype instance Ord TyVar
derive newtype instance Eq TyVar

parseType :: forall m . Monad m => ParserT String m Type'
parseType = buildPostfixParser [parseTypeArrow, parseTypeApp] parseTypeAtom 

parseTypeAtom :: forall m . Monad m => ParserT String m Type'
parseTypeAtom = defer $ \_ -> parseTypeAbs <|> ((var <<< TyVar) <$> identifier) <|> (parens parseType)

parseTypeArrow :: forall m . Monad m => Type' -> ParserT String m Type'
parseTypeArrow a = do
  reservedOp "->"
  b <- parseType
  pure (app (app (cat Arrow) a) b)


parseTypeAbs :: forall m . Monad m => ParserT String m Type'
parseTypeAbs = absMany <$> parsePats <*> parseType
  where
    parsePats = reservedOp "forall" *> many1Till (TyVar <$> identifier) (reservedOp ".")

parseTypeApp :: forall m . Monad m => Type' -> ParserT String m Type'
parseTypeApp v = app v <$> parseType


newtype UnificationState =
  UnificationState {
    nextVar :: Int
  , typingAssumptions :: Map ValVar Type'
  , currentSubstitution :: Map TyVar Type'
  }

data UnificationError =
    NotInScope ValVar
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


type Judgement = Mu (JudgementF ValVar Type')

instance VarRule var typ (JudgementF var typ (Mu (JudgementF var typ))) where
  varRule = HasType

instance AbsRule ValVar Type' (JudgementF ValVar Type') Judgement where
  absRule b t j =
    let _ /\ ret = judgement $ project j
      in JudgeAbs b j (In (App (In (App (In (Cat Arrow)) t)) ret)) 

instance TypingApplication Type' (JudgementF ValVar Type') Judgement where
  typingApplication a b t = JudgeApp a b t

instance TypingJudgement Value Type' (JudgementF ValVar Type') Judgement where
  judgement (HasType e t) = (In (Var e)) /\ t
  judgement (JudgeApp a b t) = 
    let e1 /\ _ = judgement $ project a
        e2 /\ _ = judgement $ project b
     in (In (App e1 e2)) /\ t
  judgement (JudgeAbs a b t) =
    let e2 /\ _ = judgement $ project b
     in (In (Abs a e2)) /\ t


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

runInfer' :: Value -> Either UnificationError Judgement /\ UnificationState
runInfer' v = runUnifyT (infer v)

runInfer :: Value -> Either UnificationError Type'
runInfer v = foo <$> (fst $ runUnifyT (infer v))
  where
    foo :: Judgement -> Type'
    foo j = let _ /\ t = judgement (project j) in t

runUnifyT :: forall a . UnifyT Identity a -> Either UnificationError a /\ UnificationState
runUnifyT (UnifyT f) = runState (runExceptT f) (UnificationState { nextVar: 0, typingAssumptions: Map.empty, currentSubstitution: Map.empty })


instance Monad m => Supply Type' (UnifyT m) where
  fresh = var <$> fresh

instance Monad m => Supply TyVar (UnifyT m) where
  fresh = do
    nextVar <- gets (\(UnificationState st) -> st.nextVar)
    let t = TyVar ("t" <> show nextVar)
    modify_ (\(UnificationState st) -> UnificationState st {
                  nextVar = st.nextVar + 1
                })
    pure t

instance Monad m => TypingContext ValVar Type' (UnifyT m) where
  makeAssumption v t =
     modify_ (\(UnificationState st) -> UnificationState st {
       typingAssumptions = Map.insert v t st.typingAssumptions
       })
  askEnvironment v = do
    UnificationState st <- get
    case Map.lookup v st.typingAssumptions of
      Just t -> pure t
      Nothing -> throwError $ NotInScope v

instance
  ( Monad m
  ) => Rewrite Type' (UnifyT m) where
  applyCurrentSubstitution t =
    case project t of
      Var v -> do
        UnificationState st <- get
        maybe (pure t) pure (Map.lookup v st.currentSubstitution)
      App a b -> do
        a' <- applyCurrentSubstitution a
        b' <- applyCurrentSubstitution b
        pure $ app a' b'
      Abs v a -> do
        a' <- applyCurrentSubstitution a
        -- TODO what if v gets substituted????
        pure $ abs v a'
      Cat _ -> pure t

instance
  ( Monad m
  ) => Substitution TyVar Type' (UnifyT m) where
  substitute v t' = do

     t <- applyCurrentSubstitution t'
     occursCheck v t
     u <- applyCurrentSubstitution (var v)
     case project u of
        Var v' | v' == v -> pure unit 
        _ -> do
          void $ unify u t
     -- TODO what if there is an existing substitution?
     -- we should unify
     -- TODO apply substitution to all existing substitutions
     modify_ (\(UnificationState st) -> UnificationState st {
                currentSubstitution = Map.insert v t (rewrite (\x -> if x == v then t else var x) <$> st.currentSubstitution)
              })

rewrite :: (TyVar -> Type') -> Type' -> Type'
rewrite f t =
  case project t of
    Var v -> f v
    App a b -> app (rewrite f a) (rewrite f b)
    Abs v a -> abs v (rewrite f a)
      -- TODO what if v gets substituted????
    Cat _ -> t




occursCheck :: forall m. Monad m => TyVar -> Type' -> UnifyT m Unit
occursCheck u t = do
  case project t of
    Var v -> do
      when (u == v) $ throwError $ Err $ "Occurs check"
    App a b -> do
      occursCheck u a
      occursCheck u b
    Abs v a -> do
      when (u == v) $ throwError $ Err "Occurs check"
      occursCheck u a
    Cat _ -> pure unit



instance
  ( Monad m
  , Supply TyVar (UnifyT m)
  , Substitution TyVar Type' (UnifyT m)
  , Rewrite Type' (UnifyT m)
  ) => Unify Type' (UnifyT m) where
  unify ta tb = do
     case project ta /\ project tb of
       Var a /\ Var b | a == b -> pure ta
       Var a /\ _ -> substitute a tb *> pure tb
       _ /\ Var b -> substitute b ta *> pure ta
       Abs ab aa /\ Abs bb ba -> do
         qv <- fresh
         let qty :: Type'
             qty = var qv
         substitute ab qty 
         substitute bb qty 
         ar <- applyCurrentSubstitution aa
         br <- applyCurrentSubstitution ba
         In <<< Abs qv <$> unify ar br
       App ab aa /\ App bb ba -> do
         In <$> (App <$> unify ab bb <*> unify aa ba)
       Cat ca /\ Cat cb | ca == cb -> pure ta
       _ -> throwError $ UnificationError ta tb
  unifyWithArrow t = do
     argTy <- var <$> fresh
     retTy <- var <$> fresh
     _ <- unify (In (App (In (App (In (Cat Arrow)) argTy)) retTy)) t     
     Tuple <$> applyCurrentSubstitution argTy <*> applyCurrentSubstitution retTy

  
  
