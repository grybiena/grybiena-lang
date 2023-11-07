module Language.Void.Value where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Data.Eq (class Eq1)
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, Lambda, absMany, app, prettyVar, var)
import Language.Parser.Common (buildPostfixParser, identifier, parens, reservedOp)
import Parsing (ParserT)
import Parsing.Combinators (many1Till)
import Parsing.Expr (buildExprParser)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (pretty)

newtype VoidF :: forall k. k -> Type
newtype VoidF a = VoidF Void

instance Show (VoidF a) where
  show (VoidF v) = absurd v

instance Eq1 VoidF where
  eq1 (VoidF v) = absurd v

instance Functor VoidF where
  map _ (VoidF v) = absurd v

newtype ValVar = ValVar String
derive newtype instance Show ValVar
derive newtype instance Ord ValVar
derive newtype instance Eq ValVar

type Value = Lambda ValVar VoidF

instance PrettyVar ValVar where
  prettyVar (ValVar v) = text v

instance PrettyLambda ValVar VoidF where
  prettyAbs i a = (text "\\" <> prettyVar i) <+> text "->" <+> pretty a
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat (VoidF v) = absurd v


parseValue :: forall m . Monad m => ParserT String m Value
parseValue = buildExprParser [] (buildPostfixParser [parseApp] parseValueAtom) 

parseValueAtom :: forall m . Monad m => ParserT String m Value
parseValueAtom = defer $ \_ -> parseAbs <|> ((var <<< ValVar) <$> identifier) <|> (parens parseValue)

parseAbs :: forall m . Monad m => ParserT String m Value
parseAbs = absMany <$> parsePats <*> parseValue
  where
    parsePats = reservedOp "\\" *> many1Till (ValVar <$> identifier) (reservedOp "->")

parseApp :: forall m . Monad m => Value -> ParserT String m Value
parseApp v = app v <$> parseValueAtom

