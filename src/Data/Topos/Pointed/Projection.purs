module Data.Topos.Pointed.Projection where

import Control.Alt (class Functor)
import Data.Eq (class Eq)
import Data.Foldable (class Foldable)
import Data.List (List)
import Data.Monoid (class Monoid)
import Data.Ord (class Ord)
import Data.Semigroup (class Semigroup)
import Data.Show (class Show)
import Data.Traversable (class Traversable)
 
class Functor f <= Projection f g o where
  projection :: g -> f o

newtype CC o = CC (List o)
derive newtype instance Functor CC
derive newtype instance Foldable CC
derive newtype instance Traversable CC
derive newtype instance Semigroup (CC o)
derive newtype instance Monoid (CC o)
derive newtype instance Eq o => Eq (CC o) 
derive newtype instance Ord o => Ord (CC o) 
derive newtype instance Show o => Show (CC o)


newtype SCC o = SCC (List o) 
derive newtype instance Functor SCC
derive newtype instance Foldable SCC
derive newtype instance Traversable SCC
derive newtype instance Semigroup (SCC o)
derive newtype instance Monoid (SCC o)
derive newtype instance Eq o => Eq (SCC o) 
derive newtype instance Ord o => Ord (SCC o) 
derive newtype instance Show o => Show (SCC o)


