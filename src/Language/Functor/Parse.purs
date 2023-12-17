module Language.Functor.Parse where

import Prelude

import Control.Alt (class Alt, (<|>))
import Data.Functor.Mu (Mu)
import Language.Functor.Coproduct (class Inject, type (:+:), Coproduct(..), inj)
import Language.Parser (class LanguageParser, try)
import Matryoshka (embed)

class Parse :: forall k1 k2. (k1 -> Type) -> k2 -> (k2 -> k1) -> (Type -> Type) -> Constraint
class
  ( Alt m
  ) <= Parse obj cat f m where
  parse :: m (obj (f cat)) 

instance
  ( Parse a (a :+: b) f m
  , Parse b (a :+: b) f m
  , LanguageParser m
  ) => Parse (a :+: b) (a :+: b) f m where
   parse = try (Inl <$> parse) <|> (Inr <$> parse)

instance
  ( LanguageParser m
  , Monad m
  , Parse obj (cat :+: obj) Mu m 
  , Functor cat
  , Functor obj
  , Inject obj (cat :+: obj)
  ) => Parse Mu obj (Coproduct cat) m where 
  parse = do
    (v :: obj _) <- parse
    pure $ embed (inj v)

