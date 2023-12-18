module Language.Functor.Coproduct where

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)

data Coproduct :: (Type -> Type) -> (Type -> Type) -> Type -> Type
data Coproduct f g a = Inl (f a) | Inr (g a)

instance (Show (f a), Show (g a)) => Show (Coproduct f g a) where
  show (Inl l) = show l 
  show (Inr r) = show r

instance (Functor f, Functor g) => Functor (Coproduct f g) where
  map f (Inl l) = Inl (f <$> l)
  map f (Inr r) = Inr (f <$> r)

infixr 6 type Coproduct as :+: 

class (Functor sub, Functor sup) <= Inject sub sup where
  inj :: forall a. sub a -> sup a
  prj :: forall a. sup a -> Maybe (sub a)

instance (Functor f) => Inject f f where
  inj = identity
  prj = Just
else
instance (Functor f, Functor g) => Inject f (f :+: g) where
  inj = Inl
  prj (Inl f) = Just f
  prj _ = Nothing
else
instance (Functor f, Functor g, Functor h, Inject f g) => Inject f (h :+: g) where 
  inj = Inr <<< inj
  prj (Inr g) = prj g
  prj _ = Nothing


instance (Foldable a, Foldable b) => Foldable (a :+: b) where
  foldr f b (Inl l) = foldr f b l
  foldr f b (Inr r) = foldr f b r
  foldl f b (Inl l) = foldl f b l
  foldl f b (Inr r) = foldl f b r
  foldMap f (Inl l) = foldMap f l 
  foldMap f (Inr r) = foldMap f r

instance (Traversable a, Traversable b) => Traversable (a :+: b) where
  traverse f (Inl l) = Inl <$> traverse f l 
  traverse f (Inr r) = Inr <$> traverse f r
  sequence = traverse identity 

