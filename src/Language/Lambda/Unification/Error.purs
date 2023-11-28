module Language.Lambda.Unification.Error where

import Prelude

import Control.Monad.Cont (lift)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (ExceptT)
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Language.Lambda.Calculus (LambdaF)
import Parsing (ParseError)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty)


data UnificationError f var cat =
    NotInScope var
  | Err String
  | InvalidApp (f (LambdaF var cat)) (f (LambdaF var cat)) 
  | UnificationError (f (LambdaF var cat)) (f (LambdaF var cat)) 
  | NativeTypeParseError ParseError

derive instance Generic (UnificationError f var cat) _

instance
  ( Show var
  , Show (f (LambdaF var cat))
  ) => Show (UnificationError f var cat) where
  show = genericShow

class Monad m <= ThrowUnificationError typ m where
  unificationError :: forall a. typ -> typ -> m a

instance Monad m => ThrowUnificationError (f (LambdaF var cat)) (ExceptT ParseError (ExceptT (UnificationError f var cat) m)) where 
  unificationError a b = lift $ throwError (UnificationError a b)

instance Monad m => ThrowUnificationError (f (LambdaF var cat)) (ExceptT (UnificationError f var cat) m) where 
  unificationError a b = throwError (UnificationError a b)


class Monad m <= ThrowNativeTypeParseError m where
  throwNativeTypeParseError :: forall a. ParseError -> m a

instance Monad m => ThrowNativeTypeParseError (ExceptT ParseError (ExceptT (UnificationError f var cat) m))  where
  throwNativeTypeParseError = lift <<< throwError <<< NativeTypeParseError


instance Monad m => ThrowNativeTypeParseError (ExceptT (UnificationError f var cat) m)  where
  throwNativeTypeParseError = throwError <<< NativeTypeParseError

instance
  ( Pretty var
  , Pretty (f (LambdaF var cat))
  ) => Pretty (UnificationError f var cat) where
  pretty (NotInScope v) = text "Not in scope:" <+> pretty v
  pretty (Err err) = text "Error:" <+> text err
  pretty (InvalidApp a b) = text "Invalid app:" <+> pretty a <+> pretty b
  pretty (UnificationError a b) = text "Unification error:" <+> pretty a <+> text "=?=" <+> pretty b
  pretty (NativeTypeParseError e) = text "Native type parse error:" <+> text (show e)

instance
  ( Eq var
  , Eq (f (LambdaF var cat))
  ) => Eq (UnificationError f var cat) where
  eq = genericEq

