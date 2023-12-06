module Language.Kernel.Data where


import Data.BooleanAlgebra ((&&))
import Data.Eq (class Eq, eq, (==))
import Language.Native (Native(..))
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty)
import Prim (String, Int, Record)

data Data term =
    DataApp (Data term) (Data term)
  | DataConstructor String
  | DataNative (Native term)

instance Eq (Data term) where
  eq (DataApp a b) (DataApp c d) = eq a c && eq b d
  eq (DataConstructor s) (DataConstructor q) = s == q
  eq _ _ = false

instance Pretty (Data term) where
  pretty (DataApp a b) = pretty a <+> pretty b 
  pretty (DataConstructor c) = text c
  pretty (DataNative (Purescript p)) = text p.nativePretty


