module Language.Functor.Parse where

import Prelude

import Control.Alt (class Alt, (<|>))
import Language.Functor.Coproduct (type (:+:), Coproduct(..))
import Language.Monad.Parser (class Parser, try)


class Parse :: forall k. (k -> Type) -> (k -> Type) -> k -> (Type -> Type) -> Constraint
class
  ( Alt m
  ) <= Parse obj cat f m where
   parse :: m (cat f) -> m (obj f) 

instance
  ( Parse a c f m
  , Parse b c f m
  , Parser m
  ) => Parse (a :+: b) c f m where
   parse p = (Inl <$> try (parse p)) <|> (Inr <$> (parse p))


