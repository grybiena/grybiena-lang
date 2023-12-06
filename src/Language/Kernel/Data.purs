module Language.Kernel.Data where


import Data.BooleanAlgebra ((&&))
import Data.Eq (class Eq, eq, (==))
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty)
import Prim (String, Int, Record)

data Data =
    DataApp Data Data
  | DataConstructor String

instance Eq Data where
  eq (DataApp a b) (DataApp c d) = eq a c && eq b d
  eq (DataConstructor s) (DataConstructor q) = s == q
  eq _ _ = false

instance Pretty Data where
  pretty (DataApp a b) = pretty a <+> pretty b 
  pretty (DataConstructor c) = text c


