module Test.Term where

import Prelude

import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState)
import Data.Either (Either)
import Data.Functor.Mu (Mu)
import Language.Kernel.Effect (effectNatives)
import Language.Kernel.Pure (pureModule)
import Language.Lambda.Unification (class InfiniteTypeError, class NotInScopeError, TypingContext)
import Language.Lambda.Unification.Error (class ThrowUnificationError)
import Language.Native (Native)
import Language.Native.Module (NativeModule, nativeModuleUnion)
import Language.Native.Reify (nativeModule)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Basis (runStringParserT)
import Language.Parser.Indent (IndentParserT)
import Language.Parser.Term (Parser(..), parser)
import Language.Term (TT, Term, Var)
import Parsing (ParseError)
import Parsing.String (eof)
import Type.Proxy (Proxy(..))




typeParser :: forall m.
              MonadState (TypingContext Mu Var TT) m
           => ThrowUnificationError Term m
           => InfiniteTypeError Var Term m
           => NotInScopeError Var m
           => MonadRec m
           => String -> m (Either ParseError Term) 
typeParser s = runStringParserT s do
  let someKernel = nativeModuleUnion (nativeModule pureModule) (unsafeModule (Proxy :: Proxy Parser) effectNatives)
  v <- (parser someKernel).parseType
  Parser eof
  pure v


termParser :: forall m.
              MonadState (TypingContext Mu Var TT) m
           => ThrowUnificationError Term m
           => InfiniteTypeError Var Term m
           => NotInScopeError Var m
           => MonadRec m
           => String -> m (Either ParseError Term)
termParser s = runStringParserT s do
  let mm :: NativeModule _ (IndentParserT m (Native Term))
      mm = (unsafeModule (Proxy :: Proxy Parser) effectNatives)
      someKernel = nativeModuleUnion (nativeModule pureModule) mm 
  v <- (parser someKernel).parseValue
  Parser eof
  pure v




