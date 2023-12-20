module Language.Category.Var where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad.Cofree (Cofree, (:<))
import Control.Comonad.Env (EnvT(..))
import Control.Plus (class Plus, empty)
import Data.Array as Array
import Data.CodePoint.Unicode (isUpper)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits (toCharArray)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested ((/\))
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference)
import Language.Functor.Parse (class Parse, class Postfix)
import Language.Functor.Unification (class Unification)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Context, class NotInScopeError, class Subtext, class Variable, require, rewrite, substitute)
import Language.Monad.Fresh (class Indexable)
import Language.Monad.Parser (class Parser, fail, identifier)
import Matryoshka (class Corecursive, class Recursive, embed, project)
import Type.Proxy (Proxy(..))

newtype Var :: forall k. k -> Type
newtype Var a = Var String

instance Indexable (Var a) where
  index i = Var ("v" <> show i)

instance Show (Var a) where
  show (Var v) = v

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
  ) => Inference Var Var cat (Universe u typ) m where
    inference _ (Var v) = require (Var v) >>= \t -> pure (t :< inj (Var v)) 

 

instance
  ( Monad m
  , Subtext Var (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  , Recursive (u (Cofree t)) (Cofree t)
  , Inject Var t
  , Traversable t
  ) => Unification Var Var (Universe u t) (Cofree t (Universe u t)) m where
    unification (EnvT (ta /\ (Var v))) (EnvT (tt /\ (Var w))) = do
       when (v /= w) do
         t <- rewrite (Proxy :: Proxy Var) (embed (tt :< inj (Var w))) 
         -- TODO check v not free in z
         substitute (Var v) t
       pure $ List.singleton (project ta /\ project tt) 
else
instance
  ( Monad m
  , Subtext Var (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  , Recursive (u (Cofree t)) (Cofree t)
  , Inject q t
  , Inject Var t
  , Traversable t
  ) => Unification Var q (Universe u t) (Cofree t (Universe u t)) m where
    unification (EnvT (ta /\ (Var v))) (EnvT (tt /\ t)) = do
       z <- rewrite (Proxy :: Proxy Var) (embed (tt :< inj t)) 
       -- TODO check v not free in z
       substitute (Var v) z
       pure $ List.singleton (project ta /\ project tt) 
else
instance
  ( Monad m
  , Subtext Var (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  , Recursive (u (Cofree t)) (Cofree t)
  , Inject q t
  , Inject Var t
  , Traversable t
  ) => Unification q Var (Universe u t) (Cofree t (Universe u t)) m where
    unification (EnvT (ta /\ t)) (EnvT (tt /\ (Var v))) = do
       z <- rewrite (Proxy :: Proxy Var) (embed (ta :< inj t)) 
       -- TODO check v not free in z
       substitute (Var v) z
       pure $ List.singleton (project ta /\ project tt) 

instance Variable Var where
  variable (Var v) = Var v



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

