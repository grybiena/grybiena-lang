module Language.Functor.Arrow where

class Arrow typ where
  arrow :: typ -> typ -> typ

infixr 5 arrow as :=>:
