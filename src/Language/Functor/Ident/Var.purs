module Language.Functor.Ident.Var where

import Prelude

import Control.Comonad.Cofree ((:<))
import Data.Array as Array
import Data.CodePoint.Unicode (isUpper)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits (toCharArray)
import Data.Traversable (class Traversable, traverse)
import Language.Category.Context (class Context, require)
import Language.Category.Elimination (class Elimination)
import Language.Category.Inference (class Inference)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Parse (class Parse)
import Language.Functor.Type.Universe (Universe)
import Language.Parser (class LanguageParser, fail, identifier)

newtype Var :: forall k. k -> Type
newtype Var a = Var String


class Fresh m where
  fresh :: forall (a :: Type). m (Var a)

derive instance Generic (Var a) _

instance Eq (Var a) where
  eq = genericEq

instance Functor Var where
  map _ (Var v) = Var v

instance Foldable Var where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

instance Traversable Var where
  traverse _ (Var v) = pure (Var v)
  sequence = traverse identity

instance
  ( Monad m
  , Context Var (Universe typ) m
  , Inject Var cat 
  ) => Inference Var cat (Universe typ) m where
    inference (Var v) = require (Var v) >>= \t -> pure (t :< inj (Var v)) 

instance 
  ( Monad m
  , Inject Var cat
  ) => Elimination Var cat typ m where
    elimination v t = pure (t :< inj v)

instance
  ( Monad m
  , LanguageParser m
  , Functor cat
  ) => Parse Var cat f m where
  parse = do
      i <- identifier 
      if Just false == ((isUpper <<< codePointFromChar) <$> (Array.head $ toCharArray i))
        then pure (Var i)
        else fail "Variables must not start with an upper case char."


