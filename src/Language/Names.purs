module Language.Names where

import Prelude

import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String (joinWith)

data Ident
  = Ident String
  | Op String

unIdent :: Ident -> String
unIdent (Ident i) = i
unIdent (Op op) = op

derive instance Generic Ident _
instance Show Ident where
  show = genericShow
instance Eq Ident where
  eq = genericEq
instance Ord Ident where
  compare = genericCompare


newtype ProperName = ProperName String

derive newtype instance Show ProperName
derive newtype instance Eq ProperName
derive newtype instance Ord ProperName

unProperName :: ProperName -> String
unProperName (ProperName n) = n

newtype ModuleName = ModuleName (Array ProperName)

unModuleName :: ModuleName -> String
unModuleName (ModuleName p) = joinWith "." (unProperName <$> p)

derive newtype instance Show ModuleName
derive newtype instance Eq ModuleName
derive newtype instance Ord ModuleName

data Qualified a = Qualified (Maybe ModuleName) a

derive instance Generic (Qualified a) _
instance Show a => Show (Qualified a) where
  show = genericShow
instance Eq a => Eq (Qualified a) where
  eq = genericEq
instance Ord a => Ord (Qualified a) where
  compare = genericCompare

