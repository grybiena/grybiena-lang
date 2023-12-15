module Test.Term.Eval where

import Prelude

import Control.Comonad.Cofree (head, tail)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (runExceptT)
import Control.Monad.RWS (RWSResult(..))
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState)
import Control.Monad.Writer (class MonadWriter)
import Data.Array (catMaybes, elem, nub, (!!))
import Data.Either (Either(..))
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.String (split)
import Data.String as String
import Data.Traversable (sequence, sequence_, traverse)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Debug (traceM)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Language.Lambda.Calculus (LambdaF(..), flat)
import Language.Lambda.Inference (infer)
import Language.Lambda.Judgement (Judgement)
import Language.Lambda.Reduction (elimReduce)
import Language.Lambda.Unification (class Fresh, class InfiniteTypeError, class NotInScopeError, TypingContext, runUnificationT)
import Language.Lambda.Unification.Error (class ThrowUnificationError, UnificationError)
import Language.Native (Native(..))
import Language.Parser.Term (Parser)
import Language.Term (TT(..), Var, Term)
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile, readdir)
import Parsing (ParseError)
import Pretty.Printer (prettyPrint)
import Test.Term (termParser, typeParser)
import Test.Term.Infer (structurallyEquivalent)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

evalTestSuite :: Effect Unit
evalTestSuite = do
  let dir = "fixtures/term/eval"
  ls <- readdir dir
  ts <- traverse buildCompileTest (findCompileTests dir ls)
  runTest $ suite dir $ sequence_ ts



data CompileTest = CompileTest String String
instance Show CompileTest where
  show (CompileTest te ty) = "CompileTest " <> te <> " " <> ty

findCompileTests :: String -> Array String -> Array CompileTest
findCompileTests dir a =
  let z = split (String.Pattern ".") <$> a
      x = nub $ catMaybes ((\l -> l!!0) <$> z)
      f o = 
        let te = o <> ".term"
            ty = o <> ".eval"
         in if (te `elem` a) && (ty `elem` a)
              then Just $ CompileTest (dir <> "/" <> te)  (dir <> "/" <> ty)
              else Nothing
   in catMaybes (f <$> x) 

buildCompileTest :: CompileTest -> Effect TestSuite
buildCompileTest (CompileTest te ty) = testCompileTerm te <$> (readTextFile UTF8 te) <*> (readTextFile UTF8 ty)

testCompileTerm :: String -> String -> String -> TestSuite
testCompileTerm nm v t = test nm do
  RWSResult _ res w <- (runUnificationT $ compiles v t)
  case res of
    Left (err :: UnificationError Mu Var TT) -> do
       sequence_ $ (traceM <<< prettyPrint) <$> w
       liftAff $ Assert.assert (show err) false
    Right (Left (err :: CompileError)) -> do
       sequence_ $ (liftEffect <<< log <<< prettyPrint) <$> w
       liftAff $ Assert.assert (show err) false
    Right _ -> pure unit

data CompileError =
    ReductionError String
  | TypeError String
  | ParseError ParseError
  | BasisError ParseError
  | UnifError (UnificationError Mu Var TT)

derive instance Generic CompileError _
instance Show CompileError where
  show = genericShow


compiles :: forall m.
           MonadState (TypingContext Mu Var TT) m
        => MonadWriter (List (Judgement Mu Var Var TT)) m 
        => ThrowUnificationError Term m
        => InfiniteTypeError Var Term m
        => NotInScopeError Var m
        => MonadThrow (UnificationError Mu Var TT) m
        => Fresh Int m
        => MonadRec m
        => MonadAff m
        => String -> String -> m (Either CompileError Unit) 
compiles s e = do
    t <- termParser s
    ty <- termParser e
    case Tuple <$> t <*> ty of
      Left err -> pure $ Left $ ParseError err

      Right (val /\ In (Cat (Native (Purescript exp)))) -> do
        let compileFix v = do
              let p = (Proxy :: Proxy Parser)
              q <- runExceptT do
                 i <- infer v
                 runExceptT $ elimReduce p i
              case q of
                Left err -> throwError $ UnifError err 
                Right (Left err) -> throwError $ ParseError err
                Right (Right u) -> pure u

        out' <- runExceptT $ compileFix val 
        case out' of
          Left err -> pure $ Left err 
          Right out -> do            
            case tail out of
              Cat (Native (Purescript com)) -> do
                if (unsafeCoerce com.nativeTerm :: Int) == (unsafeCoerce exp.nativeTerm :: Int) then pure $ Right unit else pure $ Left $ TypeError $ show (unsafeCoerce com.nativeTerm :: Int) <> " =?= " <> show (unsafeCoerce exp.nativeTerm :: Int) 
              _ -> pure $ Left $ ReductionError $ 
--                (prettyPrint (flat out :: Term) <> " :: " <> prettyPrint (head out))
                (show (flat out :: Term)) 
      Right _ -> pure $ Left $ TypeError "expected a native" 
