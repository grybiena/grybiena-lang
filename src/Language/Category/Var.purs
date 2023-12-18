module Language.Category.Var where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree ((:<))
import Control.Monad.State (class MonadState, modify)
import Data.Array as Array
import Data.CodePoint.Unicode (isUpper)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits (toCharArray)
import Data.Traversable (class Traversable, traverse)
import Language.Monad.Context (class Context, class NotInScopeError, Ctx(..), require)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Parse (class Parse)
import Language.Functor.Universe (Universe)
import Language.Parser (class Parser, fail, identifier)

newtype Var :: forall k. k -> Type
newtype Var a = Var String

instance Show (Var a) where
  show (Var v) = v

class Fresh m where
  fresh :: forall (a :: Type). m (Var a)

class Counter c where
  increment :: c -> c
  count :: c -> Int

instance Counter (Ctx var typ) where
  increment (Ctx c) = Ctx (c { count = c.count + 1 })
  count (Ctx c) = c.count

instance ( MonadState c m, Counter c ) => Fresh m where
  fresh = do
     i <- count <$> modify increment 
     pure $ Var ("v" <> show i)

derive instance Generic (Var a) _

instance Eq (Var a) where
  eq = genericEq

instance Ord (Var a) where
  compare = genericCompare

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
  , Context Var (Universe u typ) m
  , Inject Var cat 
  ) => Inference Var cat (Universe u typ) m where
    inference (Var v) = require (Var v) >>= \t -> pure (t :< inj (Var v)) 

instance 
  ( Monad m
  , Inject Var cat
  ) => Elimination Var cat typ m where
    elimination v t = pure (t :< inj v)

instance
  ( Monad m
  , Parser m
  , Alt m
  ) => Parse Var cat f m where
  parse _ = do
      i <- identifier 
      if Just false == ((isUpper <<< codePointFromChar) <$> (Array.head $ toCharArray i))
        then pure (Var i)
        else fail "Variables must not start with an upper case char."

instance NotInScopeError Var String where
  notInScopeError (Var v) = "not in scope: " <> v

