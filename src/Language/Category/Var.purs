module Language.Category.Var where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, (:<))
import Control.Comonad.Env (EnvT(..))
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState, modify)
import Control.Plus (class Plus, empty)
import Data.Array as Array
import Data.CodePoint.Unicode (isUpper)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits (toCharArray)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Language.Category.Hole (Hole, hole)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Unification (class Unification, unify)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Context, class NotInScopeError, Ctx(..), assume, require, substitute)
import Language.Monad.Parser (class Parser, fail, identifier)
import Matryoshka (class Corecursive, class Recursive, embed)

newtype Var :: forall k. k -> Type
newtype Var a = Var String

instance Show (Var a) where
  show (Var v) = v

class Fresh m where
  fresh :: forall (a :: Type). m (Var a)

freshHole :: forall u t m .
             Monad m
          => Inject Hole t
          => Inject Var t
          => Fresh m
          => Corecursive (u (Cofree t)) (Cofree t)
          => m (Universe u t)
freshHole = do
  t <- fresh
  pure (embed ((hole :: Universe u t) :< inj t))


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
  , Context Var (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  , Inject Var t
  ) => Unification Var Var (Universe u t) (Cofree t (Universe u t)) m where
    unification (EnvT (_ /\ (Var v))) (EnvT (tt /\ (Var w))) = do
       when (v /= w) do
         substitute (Var v) (embed (tt :< inj (Var w)))
       pure Nil 
else
instance
  ( Monad m
  , Context Var (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  , Inject q t
  ) => Unification Var q (Universe u t) (Cofree t (Universe u t)) m where
    unification (EnvT (_ /\ (Var v))) (EnvT (tt /\ t)) = do
       substitute (Var v) (embed (tt :< inj t))
       pure Nil 
else
instance
  ( Monad m
  , Context Var (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  , Inject q t
  ) => Unification q Var (Universe u t) (Cofree t (Universe u t)) m where
    unification (EnvT (tt /\ t)) (EnvT (_ /\ (Var v))) = do
       substitute (Var v) (embed (tt :< inj t))
       pure Nil 





instance 
  ( Monad m
  , Inject Var cat
  ) => Elimination Var cat typ m where
    elimination _ _ = pure Nothing 


instance
  ( Plus p
  ) => Postfix p Var cat f m where
  postfix = pure empty


instance
  ( Monad m
  , Parser m
  , Alt m
  ) => Parse Var cat f m where
  parse _ = pure do
      i <- identifier 
      if Just false == ((isUpper <<< codePointFromChar) <$> (Array.head $ toCharArray i))
        then pure (Var i)
        else fail "Variables must not start with an upper case char."

instance NotInScopeError Var String where
  notInScopeError (Var v) = "not in scope: " <> v

