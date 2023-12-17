module Language.Functor.Coproduct where

import Prelude

import Data.Maybe (Maybe(..))

data Coproduct :: (Type -> Type) -> (Type -> Type) -> Type -> Type
data Coproduct f g a = Inl (f a) | Inr (g a)

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


