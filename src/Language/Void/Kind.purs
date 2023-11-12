module Language.Void.Kind where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Except (throwError)
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, Lambda, LambdaF(..), absMany, app, cat, prettyVar, var)
import Language.Lambda.Inference (class ArrowObject)
import Language.Lambda.Unification (class Enumerable, class InfiniteTypeError, class NotInScopeError, class Unification, class UnificationError, unificationError)
import Language.Parser.Common (buildPostfixParser, identifier, parens, reservedOp)
import Language.Void.Value (Value)
import Parsing (ParserT)
import Parsing.Combinators (many1Till)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty, prettyPrint)

data KI :: forall k. k -> Type
data KI a =
    KArrow 
  | KStar


derive instance Generic (KI a) _
instance Show (KI a) where
  show = genericShow
instance Functor KI where
  map _ KArrow = KArrow
  map _ KStar = KStar
instance Eq (KI a) where
  eq  _ _ = true
instance Eq1 KI where
  eq1  _ _ = true

instance Foldable KI where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

type Kind' = Lambda KiVar KI

instance PrettyVar KiVar where
  prettyVar (KiVar v) = text v

instance Pretty KiVar where
  pretty = prettyVar

instance PrettyLambda KiVar KI where
  prettyAbs i a = text "forall" <+> (prettyVar i <> text ".") <+> pretty a
  prettyApp (In (App (In (Cat KArrow)) a)) b = text "(" <> pretty a <+> text "->" <+> pretty b <> text ")"
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat KArrow = text "->"
  prettyCat KStar = text "*"
 
newtype KiVar = KiVar String
derive newtype instance Show KiVar
derive newtype instance Ord KiVar
derive newtype instance Eq KiVar

parseKind :: forall m . Monad m => ParserT String m Kind'
parseKind = buildPostfixParser [parseKindArrow, parseKindApp] parseKindAtom 

parseKindAtom :: forall m . Monad m => ParserT String m Kind'
parseKindAtom = defer $ \_ -> parseKindAbs <|> ((var <<< KiVar) <$> identifier) <|> parseStar <|> (parens parseKind)

parseStar :: forall m . Monad m => ParserT String m Kind'
parseStar = do
  reservedOp "*"
  pure $ cat KStar

parseKindArrow :: forall m . Monad m => Kind' -> ParserT String m Kind'
parseKindArrow a = do
  reservedOp "->"
  b <- parseKind
  pure (app (app (cat KArrow) a) b)


parseKindAbs :: forall m . Monad m => ParserT String m Kind'
parseKindAbs = absMany <$> parsePats <*> parseKind
  where
    parsePats = reservedOp "forall" *> many1Till (KiVar <$> identifier) (reservedOp ".")

parseKindApp :: forall m . Monad m => Kind' -> ParserT String m Kind'
parseKindApp v = app v <$> parseKindAtom

data KindUnificationError =
    NotInScope String
  | Err String
  | InvalidApp Kind' Value
  | KindUnificationError Kind' Kind' 

derive instance Generic KindUnificationError _
instance Show KindUnificationError where
  show = genericShow
instance Eq KindUnificationError where
  eq = genericEq

instance ArrowObject (KI a) where
  arrowObject = KArrow

instance Enumerable KiVar where
  fromInt i = KiVar ("k" <> show i)

instance Pretty var => NotInScopeError var KindUnificationError where 
  notInScopeError = NotInScope <<< prettyPrint

instance InfiniteTypeError KiVar Kind' KindUnificationError where
  infiniteTypeError v t = Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v

instance UnificationError Kind' KindUnificationError where 
  unificationError = KindUnificationError 


instance
  ( Applicative m
  , UnificationError Kind' KindUnificationError
  , MonadThrow KindUnificationError m
  ) => Unification (KI Kind') m where
  unify KArrow KArrow = pure KArrow
  unify KStar KStar = pure KStar
  unify a b = throwError $ unificationError (cat a) (cat b)



