module Language.Functor.Type.Lit where

newtype Lit :: forall k. Type -> k -> Type
newtype Lit typ a = Lit typ


