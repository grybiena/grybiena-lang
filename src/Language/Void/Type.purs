module Language.Void.Type where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, Lambda, LambdaF(..), absMany, app, cat, prettyVar, var)
import Language.Lambda.Inference (class ArrowObject)
import Language.Lambda.Unification (class Enumerable, class InfiniteTypeError, class NotInScopeError, class Unification, class UnificationError)
import Language.Parser.Common (buildPostfixParser, identifier, parens, reservedOp)
import Language.Void.Value (ValVar, Value)
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

instance ArrowObject (TT a) where
  arrowObject = Arrow

instance Enumerable TyVar where
  fromInt i = TyVar ("t" <> show i)

instance NotInScopeError ValVar UnificationError where 
  notInScopeError = NotInScope

instance InfiniteTypeError TyVar Type' UnificationError where
  infiniteTypeError v t = Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v

instance UnificationError Type' UnificationError where 
  unificationError = UnificationError 


instance Applicative m => Unification (TT Type') m where
  unify Arrow Arrow = pure Arrow


