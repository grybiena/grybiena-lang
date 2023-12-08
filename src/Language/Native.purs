module Language.Native where

import Prelude

import Language.Lambda.Calculus (LambdaF)
import Pretty.Printer (class Pretty, prettyPrint)

newtype Native term = Purescript { nativeType :: term, nativePretty :: String, nativeTerm :: forall a. a }

instance Eq term => Eq (Native term) where
  eq (Purescript a) (Purescript b) = a.nativeType == b.nativeType && (a.nativeTerm :: String) == b.nativeTerm

instance Pretty term => Show (Native term) where
  show (Purescript { nativeType, nativePretty }) = "(" <> nativePretty <> " :: " <> prettyPrint nativeType <> ")"

class NativeValue f var cat where
  native :: Native (f (LambdaF var var cat))-> f (LambdaF var var cat)
  nativeCat :: forall a. Native (f (LambdaF var var cat))-> cat a 


