module Data.Topos.Pointed.Projection where

import Data.List (List)
 

class Projection :: (Type -> Type) -> Type -> Type -> Constraint
class Projection f g o where
  projection :: f g -> List o


newtype CC g = CC g

newtype SCC g = SCC g 

