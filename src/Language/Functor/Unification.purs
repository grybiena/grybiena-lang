module Language.Functor.Unification where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.List (List(..))
import Data.List as List
import Data.Traversable (traverse)
import Data.Tuple (uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Debug (traceM)
import Language.Functor.Coproduct (type (:+:), Coproduct(..))
import Language.Functor.Universe (Universe)
import Matryoshka (class Recursive, project)

class Unification l r i m where
  unification :: l i -> r i -> m (List (i /\ i)) 

instance
  ( Unification a a i m 
  , Unification b b i m 
  , Unification a b i m
  , Unification b a i m
  ) => Unification (a :+: b) (a :+: b) i m where
    unification (Inl x) (Inl y) = unification x y
    unification (Inr x) (Inr y) = unification x y
    unification (Inl x) (Inr y) = unification x y
    unification (Inr x) (Inl y) = unification x y

unify' :: forall cat t m.
         Unification cat cat (Cofree cat t) m
      => Monad m
      => cat (Cofree cat t) -> cat (Cofree cat t) -> m Unit
unify' x y = void (unifier x y)
  where
    unifier :: cat (Cofree cat t) -> cat (Cofree cat t) -> m (List (Cofree cat t))
    unifier a b = do
       join <$> (unification a b >>= (traverse (uncurry unifier) <<< map (\(f /\ g) -> tail f /\ tail g)))


unify :: forall u t m.
         Unification t t (Cofree t (Universe u t)) m
      => MonadRec m
      => Recursive (u (Cofree t)) (Cofree t) 
      => Universe u t -> Universe u t -> m Unit
unify x y = do
  let a = project x
      b = project y
  tailRecM go (List.fromFoldable [a /\ b])
  -- TODO unify the higher levels, terminating appropriately
  where
    go :: List (Cofree t (Universe u t) /\ Cofree t (Universe u t))
       -> m (Step (List (Cofree t (Universe u t) /\ Cofree t (Universe u t))) Unit)
    go Nil = pure $ Done unit
    go l = Loop <<< join <$> ((traverse (uncurry unification) <<< map (\(f /\ g) -> tail f /\ tail g)) l)






