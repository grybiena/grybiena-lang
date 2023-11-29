module Language.Kernel.Type where

import Data.BooleanAlgebra ((&&))
import Data.Eq (class Eq, eq, (==))
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty)
import Prim (String, Int, Record)

data Type =
    TypeApp Type Type
  | TypeConstructor String
  | Bottom String


instance Eq Type where
  eq (TypeApp a b) (TypeApp c d) = eq a c && eq b d
  eq (TypeConstructor s) (TypeConstructor q) = s == q
  eq _ _ = false

instance Pretty Type where
  pretty (TypeApp a b) = pretty a <+> pretty b 
  pretty (TypeConstructor c) = text c
  pretty (Bottom s) = text "Error:" <+> text s

primitiveTypeConstructors :: Record 
  ( "Int" :: Type
  , "Number" :: Type
  , "Boolean" :: Type
  , "Effect" :: Type -> Type
  , "Maybe" :: Type -> Type
  )
primitiveTypeConstructors = 
  { "Int": TypeConstructor "Int"
  , "Number": TypeConstructor "Number"
  , "Boolean": TypeConstructor "Boolean"
  , "Effect": TypeApp (TypeConstructor "Effect")
  , "Maybe": TypeApp (TypeConstructor "Maybe")
  }

