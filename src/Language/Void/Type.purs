module Language.Void.Type where

import Prelude

import Control.Alt ((<|>))
import Control.Comonad.Cofree (Cofree, head)
import Control.Lazy (defer)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Except.Trans (class MonadThrow)
import Control.Monad.State (class MonadState, StateT, get, gets, modify_, runState)
import Data.Either (Either)
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\))
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, class Substitute, Lambda, LambdaF(..), absMany, app, cat, occursIn, prettyVar, replace, rewrite, var)
import Language.Lambda.Inference (class ArrowObject, class Context, class Fresh, class UnificationError, class Unify, fresh, infer, unify)
import Language.Parser.Common (buildPostfixParser, identifier, parens, reservedOp)
import Language.Void.Value (ValVar, Value, VoidF)
import Matryoshka.Class.Recursive (project)
import Parsing (ParserT)
import Parsing.Combinators (many1Till)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (pretty, prettyPrint)

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

instance Foldable TT where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty


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
parseTypeApp v = app v <$> parseTypeAtom


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
instance Eq UnificationError where
  eq = genericEq
newtype UnifyT m a = UnifyT (ExceptT UnificationError (StateT UnificationState m) a)
derive newtype instance Functor m => Functor (UnifyT m)
derive newtype instance Monad m => Apply (UnifyT m)
derive newtype instance Monad m => Applicative (UnifyT m)
derive newtype instance Monad m => Bind (UnifyT m)
derive newtype instance Monad m => Monad (UnifyT m)
derive newtype instance Monad m => MonadState UnificationState (UnifyT m)
derive newtype instance Monad m => MonadThrow UnificationError (UnifyT m)

type Judgement = Cofree (LambdaF ValVar VoidF) Type'

instance ArrowObject (TT a) where
  arrowObject = Arrow

runInfer' :: Value -> Either UnificationError Judgement /\ UnificationState
runInfer' v = runUnifyT (infer v)

runInfer :: Value -> Either UnificationError Type'
runInfer v = foo <$> (fst $ runUnifyT (infer v))
  where
    foo :: Judgement -> Type'
    foo j = let t = head j in t

runUnifyT :: forall a . UnifyT Identity a -> Either UnificationError a /\ UnificationState
runUnifyT (UnifyT f) = runState (runExceptT f) (UnificationState { nextVar: 0, typingAssumptions: Map.empty, currentSubstitution: Map.empty })


instance Monad m => Fresh Type' (UnifyT m) where
  fresh = var <$> fresh

instance Monad m => Fresh TyVar (UnifyT m) where
  fresh = do
    nextVar <- gets (\(UnificationState st) -> st.nextVar)
    let t = TyVar ("t" <> show nextVar)
    modify_ (\(UnificationState st) -> UnificationState st {
                  nextVar = st.nextVar + 1
                })
    pure t

instance Monad m => Context ValVar Type' (UnifyT m) where
  assume v t =
     modify_ (\(UnificationState st) -> UnificationState st {
       typingAssumptions = Map.insert v t st.typingAssumptions
       })
  require v = do
    UnificationState st <- get
    case Map.lookup v st.typingAssumptions of
      Just t -> pure t
      Nothing -> throwError $ NotInScope v

instance
  ( Monad m
  ) => Substitute TyVar TT Mu (UnifyT m) where
  substitute v t' = do

     t <- rewrite t'
     when (v `occursIn` t) $ throwError $ Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v
     u <- rewrite (var v)
     case project u of
        Var v' | v' == v -> pure unit 
        _ -> do
          void $ unify u t
     -- apply new substitution to all existing substitutions
     modify_ (\(UnificationState st) -> UnificationState st {
                currentSubstitution = Map.insert v t (replace (\x -> if x == v then Just t else Nothing) <$> st.currentSubstitution)
              })
  substitution = do
    UnificationState st <- get
    pure $ flip Map.lookup st.currentSubstitution

instance Applicative m => Unify (TT Type') m where
  unify Arrow Arrow = pure Arrow

instance Monad m => UnificationError Type' (UnifyT m) where 
  unificationError t = throwError <<< UnificationError t

