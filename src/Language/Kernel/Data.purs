module Language.Kernel.Data where


import Data.BooleanAlgebra ((&&))
import Data.Eq (class Eq, eq, (==))
import Data.Maybe (Maybe)
import Data.Show (class Show)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty, prettyPrint)
import Prim (String, Int, Record)

data Data term =
    DataApp (Data term) (Data term)
  | DataConstructor String (Maybe term)
  | DataNative (forall a . a)

instance Eq (Data term) where
  eq (DataApp a b) (DataApp c d) = eq a c && eq b d
  eq (DataConstructor s _) (DataConstructor q _) = s == q
  eq _ _ = false

instance Pretty (Data term) where
  pretty (DataApp a b) = pretty a <+> pretty b 
  pretty (DataConstructor c _) = text c
  pretty (DataNative _) = text "DataNative" 

instance Pretty term => Show (Data term) where
  show = prettyPrint

