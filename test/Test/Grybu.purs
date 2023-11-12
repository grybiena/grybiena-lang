module Test.Grybu where

import Prelude

import Control.Comonad.Cofree ((:<))
import Data.Either (Either(..))
import Data.Identity (Identity(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Language.Grybu (TT(..), Term, UnificationError(..), Var(..), int, num, parseType, parseValue)
import Language.Lambda.Calculus (universe)
import Language.Lambda.Inference (runInference)
import Language.Lambda.Unification (rewrite, runUnification, unify)
import Machine.Closure (closure)
import Machine.Krivine (Halt(..), runUnbounded)
import Parsing (ParseError, runParserT)
import Parsing.Indent (runIndent)
import Parsing.String (eof)
import Pretty.Printer (prettyPrint)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

grybuTests :: Effect Unit
grybuTests = runTest do
  suite "Language.Void" do

    testExpectErr "x" (NotInScope $ TermVar "x")

    testExpectErr "\\x -> x x" $
                  Err "An infinite type was inferred for an expression: (t2 -> t3) while trying to match type t2" 

    testExpectErr "\\f -> (\\x -> f (x x)) (\\x -> f (x x))" $
                  Err "An infinite type was inferred for an expression: (t3 -> t4) while trying to match type t3"
    testInferType "\\x -> x" "a -> a"
    testInferTypeThenKind "\\x -> x" "a -> a"

    testInferType "\\x y -> x" "a -> b -> a"
    testInferType "\\x y -> y" "a -> b -> b"
    testInferType "\\x y -> x y" "(a -> b) -> a -> b"
    testInferType "\\x y -> y x" "a -> (a -> b) -> b"
    testInferType "\\x y z -> (x z) (y z)" "(a -> b -> c) -> (a -> b) -> a -> c"
    testInferType "\\x y z -> x z (y z)" "(a -> b -> c) -> (a -> b) -> a -> c"

    testInferType "1" "Int"
    testInferType "1.0" "Number"

    testInferType "intPlus 1 1" "Int"
    testInferType "intPlus 1" "Int -> Int"
    testInferType "intPlus" "Int -> Int -> Int"

    testInferType "1 :: Int" "Int"
    testInferType "\\a -> a :: Int" "Int -> Int"

    testInferType "1 :: Int :: *" "Int" 



    testInferKind "forall a . a" "k -> k"
    testInferKind "forall a b. a b" "(k -> j) -> (k -> j)" 
    testInferKind "forall a b. b a" "k -> (k -> j) -> j" 
    testInferKind "forall a . a -> a" "* -> *"
    testInferKind "forall a b . a -> b" "* -> * -> *"

    testInferKind "*" "**"
    testInferKind "* -> *" "*"
    testInferKind "* :: ** :: *** :: ****" "*"
    testInferKind "* :: ** :: *** :: ****" "**"
    testInferKind "****" "*"

    testInferKind "Int" "*"
    testInferKind "Number" "*"


    testRun "1" (Native $ int 1)
    testRun "1.0" (Native $ num 1.0)
    testRun "intPlus 1 1" (Native $ int 2)
    testRun "intPlus (intPlus 1 1) (intPlus 1 1)" (Native $ int 4)

    testRun "numPlus 1.0 1.0" (Native $ num 2.0)

    testRun "numPlus (numPlus 99.9 0.001) (numPlus 0.0004 0.0005)" (Native $ num 99.90190000000001)

--    testRun "intPlus (1 1)" (Native $ int 4)


-- Pure
    testInferType "pureEffect" "(forall a. a -> (Effect a))"
    testInferType "pureEffect @Int" "Int -> Effect Int"

    testInferTypeThenKind "pureEffect @Int" "*"

    testInferTypeThenKind "pureEffect 1" "Int -> Effect Int"

    testRun "pureEffect @Int 1" (Native $ int 1)

    testRun "bindEffect @Int @Int (pureEffect @Int 1) (pureEffect @Int)" (Native $ int 1)
 
    -- TODO this causes a stack fault since evaluation of the lambda expects an argument on the stack
    -- and the machine cannot halt on the lambda
    -- bindEffect must work at the machine level, evaluating the first argument, then placing it on
    -- the stack for consumption by the second argument
    -- ALT instead of a stack fault we should bind a callback in a Comonadic way 
    -- i.e. reverse the semantics of application, whenever a Native is applied to a callback
    -- we unwrap the callback and realise that we have to apply the callback to the native
    -- i.e we end up applying (pureEffect ~ Native :: Int -> Effect Int) to (Callback :: (a -> x) -> x) 
    -- which resolves by applying the callback to the native
    -- resulting in a (Native :: Effect Int)

    testRun "bindEffect @Int @Int (pureEffect @Int 1) (\\a -> pureEffect @Int a)" (Native $ int 1)


-- Bind
    testInferType "bindEffect" "forall b a. Effect a -> (a -> Effect b) -> Effect b"
    testInferType "bindEffect" "forall a b. Effect a -> (a -> Effect b) -> Effect b"


    -- TODO this should fail
    testInferType "bindEffect" "forall x y. Effect a -> (a -> Effect b) -> Effect b"




testInferType :: String -> String -> TestSuite
testInferType v t = test ("(" <> v <> ") :: " <> t) do
  case Tuple <$> termParser v <*> typeParser t of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right ((val :: Term Identity) /\ (typ :: Term Identity)) -> do
      case runInference val of
        Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false
        Right suc ->
          case alphaEquivalent suc typ of
            Right b -> Assert.assert ("Expected to unify with: " <> prettyPrint suc) b
            Left err -> Assert.assert ("unification error: " <> prettyPrint suc <> " | " <> prettyPrint err) false


testInferTypeThenKind :: String -> String -> TestSuite
testInferTypeThenKind v k = test ("(" <> v <> ") :: " <> k) do
  case Tuple <$> termParser v <*> typeParser k of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right ((val :: Term Identity) /\ (kin :: Term Identity)) -> do
      case runInference val of
        Left (err :: UnificationError Identity) -> Assert.assert ("type infer error: " <> prettyPrint err) false
        Right (typ :: Term Identity) ->
          case runInference typ of
            Left (err :: UnificationError Identity) -> Assert.assert ("kind infer error: " <> prettyPrint err) false
            Right suc ->
              case alphaEquivalent suc kin of
                Left err -> Assert.assert ("unification error: " <> prettyPrint suc <> " | " <> prettyPrint err) false
                Right b -> Assert.assert ("Expected to unify with: " <> prettyPrint suc) b



testRun :: String -> TT Identity Void -> TestSuite
testRun v h = test ("run (" <> v <> ")") do
  case termParser v of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right val -> do
      case runUnbounded (closure val Map.empty :< Nothing) of
        res | res == Identity (Halt h) -> pure unit
        res -> Assert.assert (show res) false
 
 

testInferKind :: String -> String -> TestSuite
testInferKind v t = test ("(" <> v <> ") :: " <> t) do
  case Tuple <$> typeParser v <*> typeParser t of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right ((val :: Term Identity) /\ (typ :: Term Identity)) -> do
      case runInference val of
        Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false
        Right suc ->
          case alphaEquivalent suc typ of
            Right b -> Assert.assert ("Expected to unify with: " <> prettyPrint suc) b
            Left err -> Assert.assert ("unification error: " <> prettyPrint suc <> " | " <> show err) false



testExpectErr :: String -> UnificationError Identity -> TestSuite
testExpectErr v e = test ("(" <> v <> ") :: _|_") do
  case termParser v of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right (val :: Term Identity) -> do
      case runInference val of
        Left e' -> Assert.equal e e'
        Right (_ :: Term Identity) -> Assert.assert "Expected failure but got success" false


alphaEquivalent :: forall m. Term m -> Term m -> Either (UnificationError m ) Boolean
alphaEquivalent t1 t2 = do
  a <- fst do 
    runUnification do
       _ <- unify t2 t1
       x <- rewrite t2
       y <- rewrite t1
       pure  (universe x == universe y)
  b <- fst do
    runUnification do
       _ <- unify t1 t2
       x <- rewrite t1
       y <- rewrite t2
       pure  (universe x == universe y)
  pure (a && b)


typeParser :: forall m. String -> Either ParseError (Term m)
typeParser s = runIndent $ runParserT s do
  v <- parseType
  eof
  pure v


termParser :: forall m. Monad m => String -> Either ParseError (Term m)
termParser s = runIndent $ runParserT s do
  v <- parseValue
  eof
  pure v


