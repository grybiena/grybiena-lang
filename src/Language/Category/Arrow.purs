module Language.Category.Arrow where

class Arrow typ where
  arrow :: typ -> typ -> typ

infixr 5 arrow as :=>:
