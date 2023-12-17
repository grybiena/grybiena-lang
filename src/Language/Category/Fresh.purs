module Language.Category.Fresh where


class Fresh a m where
  fresh :: m a


