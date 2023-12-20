module Language.Functor.Unification where

import Prelude

import Control.Comonad.Cofree (Cofree, (:<))
import Control.Comonad.Env (EnvT(..), runEnvT)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.List (List(..))
import Data.List as List
import Data.Traversable (traverse)
import Data.Tuple (uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Functor.Coproduct (class Inject, type (:+:), Coproduct(..), inj)
import Language.Functor.Universe (Universe, flatten)
import Matryoshka (class Corecursive, class Recursive, embed, project)

type Layer a u t = EnvT (Universe u t) a (Cofree t (Universe u t))

class UnificationError a b err where
  unificationError :: a -> b -> err

instance
  ( Functor t
  , Inject a t
  , Inject b t
  , Corecursive (u (Cofree t)) (Cofree t)
  , Corecursive (u t) t
  , Recursive (u (Cofree t)) (Cofree t)
  , Show (u t)
  ) => UnificationError (Layer a u t) (Layer b u t) String where
  unificationError (EnvT (ta /\ a)) (EnvT (tb /\ b)) =
    "unification error: " <> show (flatten (embed (ta :< inj a))) <> " =?= " <> show (flatten (embed (tb :< inj b)))


class Unification l r t i m where
  unification :: EnvT t l i -> EnvT t r i -> m (List (i /\ i)) 

instance
  ( Unification a a t i m 
  , Unification b b t i m 
  , Unification a b t i m
  , Unification b a t i m
  ) => Unification (a :+: b) (a :+: b) t i m where
    unification l r =
      case runEnvT l /\ runEnvT r of
        (tl /\ Inl x) /\ (tr /\ Inl y) -> unification (EnvT (tl /\ x)) (EnvT (tr /\ y))
        (tl /\ Inr x) /\ (tr /\ Inr y) -> unification (EnvT (tl /\ x)) (EnvT (tr /\ y))
        (tl /\ Inl x) /\ (tr /\ Inr y) -> unification (EnvT (tl /\ x)) (EnvT (tr /\ y))
        (tl /\ Inr x) /\ (tr /\ Inl y) -> unification (EnvT (tl /\ x)) (EnvT (tr /\ y))

unify :: forall u t m.
         Unification t t (Universe u t) (Cofree t (Universe u t)) m
      => MonadRec m
      => Recursive (u (Cofree t)) (Cofree t) 
      => Functor t
      => Universe u t -> Universe u t -> m Unit
unify x y = do
  let a = project x
      b = project y
  tailRecM go (List.fromFoldable [a /\ b])
  -- TODO unify higher levels, terminating appropriately
  where
    go :: List (Cofree t (Universe u t) /\ Cofree t (Universe u t))
       -> m (Step (List (Cofree t (Universe u t) /\ Cofree t (Universe u t))) Unit)
    go Nil = pure $ Done unit
    go l = Loop <<< join <$> ((traverse (uncurry unification) <<< map (\(f /\ g) -> project f /\ project g)) l)






