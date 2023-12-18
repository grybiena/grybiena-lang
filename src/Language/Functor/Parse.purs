module Language.Functor.Parse where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Lazy (class Lazy, fix)
import Data.List (List)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple.Nested ((/\))
import Language.Functor.Coproduct (type (:+:), Coproduct(..))
import Language.Monad.Parser (class Parser, choice, fail, optionMaybe, parens, try)


class
  ( Functor p
  , Functor obj
  ) <= Postfix p obj cat f m where
  postfix :: m (cat f) -> p (cat f -> m (obj f))

instance
  ( Postfix p a c f m
  , Postfix p b c f m
  , Functor m
  , Semigroup (p (c f -> m ((a :+: b) f)))
  , Functor p
  ) => Postfix p (a :+: b) c f m where
   postfix p = (compose (map Inl) <$> postfix p) <> (compose (map Inr) <$> postfix p)

class Parse :: forall k. (k -> Type) -> (k -> Type) -> k -> (Type -> Type) -> Constraint
class
  ( Alt m
  ) <= Parse obj cat f m where
   parse :: m (cat f) -> Maybe (m (obj f)) 

instance
  ( Parse a c f m
  , Parse b c f m
  , Parser m
  ) => Parse (a :+: b) c f m where
   parse p =
     case parse p /\ parse p of
       Just a /\ Just b -> Just $ (Inl <$> try a) <|> (Inr <$> b)
       Just a /\ Nothing -> Just (Inl <$> a)
       Nothing /\ Just b -> Just (Inr <$> b)
       Nothing /\ Nothing -> Nothing

parseable :: forall obj cat f m .
             Parser m
          => Parse obj cat f m
          => m (cat f) -> m (obj f)
parseable p = maybe (fail "Not a parseable object.") identity (parse p)

parser :: forall cat f m.
          Postfix List cat cat f m
       => Parse cat cat f m
       => Parser m
       => Lazy (m (cat f)) 
       => m (cat f)
parser = fix post
  where
    post :: m (cat f) -> m (cat f)
    post p = catom >>= fixPost
      where
        catom = maybe (fail "Category is not parseable.") identity (parse p)
        atom =  catom <|> parens p
        fixPost a = do
          let postFixes :: List (m (cat f))
              postFixes = map (flip ($) a) (postfix atom)
          maybe (pure a) fixPost =<< optionMaybe (choice postFixes)
    

