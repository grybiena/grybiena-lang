module Language.Monad.Fresh where


class Fresh a m where
  fresh :: m a


