module Language.Kernel.Constraint where

import Language.Kernel.Type (Type)
import Prim (String, Int, Record)

-- idk

data Constraint =
    ConstraintConstructor String
  | ConstraintApp Constraint Type

primitiveConstraintConstructors :: Record
  ( "Semigroup" :: Type -> Constraint
  )
primitiveConstraintConstructors = 
  { "Semigroup": ConstraintApp (ConstraintConstructor "Semigroup")
  }
