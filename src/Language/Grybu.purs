module Language.Grybu where

import Prelude

import Control.Alt ((<|>))
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Lazy (defer)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (class MonadState)
import Data.Array (replicate, (..))
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (fromCharArray)
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, Lambda, LambdaF(..), absMany, app, cat, prettyVar, var)
import Language.Lambda.Inference (class ArrowObject, class Inference, arrow)
import Language.Lambda.Unification (class Enumerable, class Fresh, class InfiniteTypeError, class NotInScopeError, class Unification, class UnificationError, TypingContext, unificationError, unify)
import Language.Parser.Common (buildPostfixParser, identifier, integer, number, parens, reserved, reservedOp)
import Parsing (ParserT)
import Parsing.Combinators (choice, many1Till, try)
import Parsing.Expr (buildExprParser)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (pretty, prettyPrint)

type Term = Lambda Var TT


data TT a =
    Arrow 
  | Star Int

  | TypeAnnotation a Term

  | Int Int
  | TypeInt

  | Number Number
  | TypeNumber

derive instance Generic (TT a) _

instance Show a => Show (TT a) where
  show (TypeAnnotation a t) = "TypeAnnotation " <> show a <> " " <> show t
  show e = genericShow e


instance Functor TT where
  map _ Arrow = Arrow
  map _ (Star i) = Star i
  map f (TypeAnnotation a t) = TypeAnnotation (f a) t
  map _ (Int i) = Int i
  map _ TypeInt = TypeInt
  map _ (Number n) = Number n
  map _ TypeNumber = TypeNumber


instance Eq a => Eq (TT a) where
  eq = genericEq

instance Eq1 TT where
  eq1 = genericEq

instance Foldable TT where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

data Var =
    TypeVar String
  | TermVar String

derive instance Generic Var _
instance Show Var where
  show = genericShow
instance Ord Var where
  compare = genericCompare
instance Eq Var where
  eq = genericEq

instance PrettyVar Var where
  prettyVar (TypeVar v) = text v
  prettyVar (TermVar v) = text v

instance PrettyLambda Var TT where
  prettyAbs (TermVar i) a = (text "\\" <> prettyVar i) <+> text "->" <+> pretty a
  prettyAbs (TypeVar i) a = (text "forall" <> prettyVar i) <+> text "." <+> pretty a
  prettyApp (In (App (In (Cat Arrow)) a)) b = text "(" <> pretty a <+> text "->" <+> pretty b <> text ")"
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat Arrow = text "->"
  prettyCat (Star i) = text (fromCharArray $ replicate i '*')
  prettyCat (TypeAnnotation v t) = text "(" <> pretty v <+> text "::" <+> pretty t <> text ")"
  prettyCat (Int i) = text $ show i
  prettyCat TypeInt = text "Int"
  prettyCat (Number i) = text $ show i
  prettyCat TypeNumber = text "Number"

parseValue :: forall m . Monad m => ParserT String m Term
parseValue = buildExprParser [] (buildPostfixParser [parseApp, parseTypeAnnotation] parseValueAtom) 

parseValueAtom :: forall m . Monad m => ParserT String m Term
parseValueAtom = defer $ \_ -> parseAbs <|> ((var <<< TermVar) <$> identifier) <|> parseNumeric <|> (parens parseValue)

parseNumeric :: forall m . Monad m => ParserT String m Term
parseNumeric = (try parseNumber) <|> parseInt

parseInt :: forall m . Monad m => ParserT String m Term
parseInt = cat <<< Int <$> integer
 
parseNumber :: forall m . Monad m => ParserT String m Term
parseNumber = cat <<< Number <$> number

parseTypeAnnotation :: forall m . Monad m => Term -> ParserT String m Term
parseTypeAnnotation v = do
  reservedOp "::"
  t <- parseType
  pure $ cat $ TypeAnnotation v t
 
parseAbs :: forall m . Monad m => ParserT String m Term
parseAbs = absMany <$> parsePats <*> parseValue
  where
    parsePats = reservedOp "\\" *> many1Till (TermVar <$> identifier) (reservedOp "->")

parseApp :: forall m . Monad m => Term -> ParserT String m Term
parseApp v = app v <$> parseValueAtom

parseType :: forall m . Monad m => ParserT String m Term
parseType = buildPostfixParser [parseTypeArrow, parseTypeApp, parseTypeAnnotation] parseTypeAtom 

parseTypeAtom :: forall m . Monad m => ParserT String m Term
parseTypeAtom = defer $ \_ -> parseTypeAbs <|> ((var <<< TypeVar) <$> identifier) <|> parseStar <|> parseTypeInt <|> parseTypeNumber <|> (parens parseType)

parseTypeInt :: forall m . Monad m => ParserT String m Term
parseTypeInt = reserved "Int" *> pure (cat TypeInt)
 
parseTypeNumber :: forall m . Monad m => ParserT String m Term
parseTypeNumber = reserved "Number" *> pure (cat TypeNumber)
 

parseTypeArrow :: forall m . Monad m => Term -> ParserT String m Term
parseTypeArrow a = do
  reservedOp "->"
  b <- parseType
  pure (app (app (cat Arrow) a) b)

parseStar :: forall m . Monad m => ParserT String m Term
parseStar = choice (star <$> (1 .. 4))
  where
    star i = do
      reservedOp (fromCharArray (replicate i '*'))
      pure $ cat (Star i)

parseTypeAbs :: forall m . Monad m => ParserT String m Term
parseTypeAbs = absMany <$> parsePats <*> parseType
  where
    parsePats = reservedOp "forall" *> many1Till (TypeVar <$> identifier) (reservedOp ".")

parseTypeApp :: forall m . Monad m => Term -> ParserT String m Term
parseTypeApp v = app v <$> parseTypeAtom


data UnificationError =
    NotInScope Var
  | Err String
  | InvalidApp Term Term
  | UnificationError Term Term 

derive instance Generic UnificationError _
instance Show UnificationError where
  show = genericShow
instance Eq UnificationError where
  eq = genericEq

instance ArrowObject (TT a) where
  arrowObject = Arrow

instance Enumerable Var where
  fromInt i = TypeVar ("t" <> show i)

instance NotInScopeError Var UnificationError where 
  notInScopeError = NotInScope

instance InfiniteTypeError Var Term UnificationError where
  infiniteTypeError v t = Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v

instance UnificationError Term UnificationError where 
  unificationError = UnificationError 


instance
  ( MonadThrow UnificationError m
  , Fresh Var m
  , MonadState (TypingContext Var Mu Var TT) m
  ) => Unification (TT Term) m where
  unify Arrow Arrow = pure Arrow
  -- TODO concerned that our hierarchy of type universes may permit paradox
  -- should the type of the arrow be the max of the types of the domain/codomain i.e. (* -> * :: **)
  -- currently it is always * which is simple but probably wrong for some definition of wrong 
  -- TODO read more about Girard's paradox and implementations of cumulativity constraints
  unify (Star i) (Star j) = pure $ Star (max i j)
  unify (TypeAnnotation a ak) (TypeAnnotation b bk) = flip TypeAnnotation <$> unify ak bk  <*> unify a b
  unify (TypeAnnotation a k) b = flip TypeAnnotation k <$> unify a (cat b)
  unify a (TypeAnnotation b k) = flip TypeAnnotation k <$> unify (cat a) b
  unify TypeInt TypeInt = pure TypeInt
  unify TypeNumber TypeNumber = pure TypeNumber
  unify a b = throwError $ unificationError (cat a) (cat b)


instance
  ( Monad m
  , Unification Term m
  ) => Inference Var TT Term m where
  inference Arrow = pure $ (arrow (cat (Star 1)) (arrow (cat (Star 1)) (cat (Star 1))) :< Cat Arrow)
  inference (Star i) = pure $ (cat (Star (i+1)) :< Cat (Star i))
  inference (TypeAnnotation v t) = do
    (t' :: Cofree (LambdaF Var TT) Term) <- v
    _ <- unify (t :: Term) (head t' :: Term)
    pure (t :< tail t')
  inference (Int i) = pure $ (cat TypeInt :< Cat (Int i))
  inference TypeInt = pure $ (cat (Star 1) :< Cat TypeInt)
  inference (Number n) = pure $ cat TypeNumber :< Cat (Number n)
  inference TypeNumber = pure $ cat (Star 1) :< Cat TypeNumber





