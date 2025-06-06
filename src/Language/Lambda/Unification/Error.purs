module Language.Lambda.Unification.Error where

import Prelude

import Control.Monad.Cont (class MonadTrans, lift)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (ExceptT)
import Data.Array (intercalate)
import Data.Array as Array
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Map as Map
import Data.Show.Generic (genericShow)
import Language.Lambda.Calculus (LambdaF)
import Language.Lambda.Module (Module(..))
import Parsing (ParseError)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty)


data UnificationError f var cat =
    NotInScope var
  | Err String
  | InvalidApp (f (LambdaF var var cat)) (f (LambdaF var var cat)) 
  | UnificationError (f (LambdaF var var cat)) (f (LambdaF var var cat)) 
  | NativeTypeParseError ParseError
  | RecursiveModuleError (Module var (f (LambdaF var var cat)))

derive instance Generic (UnificationError f var cat) _

instance
  ( Show var
  , Show (f (LambdaF var var cat))
  ) => Show (UnificationError f var cat) where
  show = genericShow

class Monad m <= ThrowRecursiveModuleError f var cat m where
  recursiveModuleError :: forall a. Module var (f (LambdaF var var cat) )-> m a

class Monad m <= ThrowUnificationError typ m where
  unificationError :: forall a. typ -> typ -> m a

instance Monad m => ThrowRecursiveModuleError f var cat (ExceptT ParseError (ExceptT (UnificationError f var cat) m)) where 
  recursiveModuleError = lift <<< recursiveModuleError

instance Monad m => ThrowRecursiveModuleError f var cat (ExceptT (UnificationError f var cat) m) where 
  recursiveModuleError = throwError <<< RecursiveModuleError



instance Monad m => ThrowUnificationError (f (LambdaF var var cat)) (ExceptT (UnificationError f var cat) m) where 
  unificationError a b = throwError (UnificationError a b)
else
instance
  ( Monad (t m)
  , ThrowUnificationError (f (LambdaF var var cat)) m
  , MonadTrans t
  ) =>  ThrowUnificationError (f (LambdaF var var cat)) (t m) where 
  unificationError a b = lift $ unificationError a b



class Monad m <= ThrowNativeTypeParseError m where
  throwNativeTypeParseError :: forall a. ParseError -> m a

instance Monad m => ThrowNativeTypeParseError (ExceptT ParseError (ExceptT (UnificationError f var cat) m))  where
  throwNativeTypeParseError = lift <<< throwError <<< NativeTypeParseError


instance Monad m => ThrowNativeTypeParseError (ExceptT (UnificationError f var cat) m)  where
  throwNativeTypeParseError = throwError <<< NativeTypeParseError

instance
  ( Pretty var
  , Pretty (f (LambdaF var var cat))
  ) => Pretty (UnificationError f var cat) where
  pretty (NotInScope v) = text "Not in scope:" <+> pretty v
  pretty (Err err) = text "Error:" <+> text err
  pretty (InvalidApp a b) = text "Invalid app:" <+> pretty a <+> pretty b
  pretty (UnificationError a b) = text "Unification error:" <+> pretty a <+> text "=?=" <+> pretty b
  pretty (NativeTypeParseError e) = text "Native type parse error:" <+> text (show e)
  pretty (RecursiveModuleError (Module lr)) =
    text "Recursive bindings are not allowed:" <+> text "[" <> (intercalate (text ",") (pretty <$> (Array.fromFoldable $ Map.keys lr))) <> text "]"

instance
  ( Eq var
  , Eq (f (LambdaF var var cat))
  ) => Eq (UnificationError f var cat) where
  eq = genericEq

