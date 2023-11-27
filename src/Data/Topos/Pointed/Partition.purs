module Data.Topos.Pointed.Partition where

import Data.List (List)
 

class Partition :: (Type -> Type) -> Type -> Type -> Constraint
class Partition f g o where
  partition :: f g -> List o


newtype CC o = CC o

newtype SCC o = SCC o 

