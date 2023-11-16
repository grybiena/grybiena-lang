module Language.Value.Native where

import Prelude

import Pretty.Printer (class Pretty, prettyPrint)
import Unsafe.Coerce (unsafeCoerce)

newtype Native term = Purescript { nativeType :: term, nativeTerm :: forall a. a }



instance Eq term => Eq (Native term) where
  eq (Purescript a) (Purescript b) = a.nativeType == b.nativeType && (a.nativeTerm :: String) == b.nativeTerm

instance Pretty term => Show (Native term) where
  show (Purescript { nativeType, nativeTerm }) = "(" <> unsafeCoerce nativeTerm <> " :: " <> prettyPrint nativeType <> ")"

