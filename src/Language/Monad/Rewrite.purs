module Language.Monad.Rewrite where

class Rewrite a m where
  rewrite :: a -> m a
