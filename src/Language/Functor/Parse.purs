module Language.Functor.Parse where

import Prelude

import Control.Alt (class Alt, (<|>))
import Data.Functor.Coproduct.Inject (inj)
import Data.Functor.Mu (Mu, transMu)
import Language.Functor.Coproduct (type (:+:), Coproduct(..))
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
  ( Monad m
  , Parse obj cat Mu m 
  , Functor obj
  , Functor cat
  ) => Parse Mu cat (Coproduct obj) m where 
  parse = embed <<< Inl <<< map (transMu Inr) <$> parse 



