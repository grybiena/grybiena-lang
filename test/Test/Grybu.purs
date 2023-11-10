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
import Language.Grybu (GHalt(..), Term, UnificationError(..), Var(..), parseType, parseValue)
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
    testInferType "\\x y -> x" "a -> b -> a"
    testInferType "\\x y -> y" "a -> b -> b"
    testInferType "\\x y -> x y" "(a -> b) -> a -> b"
    testInferType "\\x y -> y x" "a -> (a -> b) -> b"
    testInferType "\\x y z -> (x z) (y z)" "(a -> b -> c) -> (a -> b) -> a -> c"
    testInferType "\\x y z -> x z (y z)" "(a -> b -> c) -> (a -> b) -> a -> c"

    testInferType "1" "Int"
    testInferType "1.0" "Number"

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


    testRun "1" (PureInt 1)
    testRun "1.0" (PureNumber 1.0)

testInferType :: String -> String -> TestSuite
testInferType v t = test ("(" <> v <> ") :: " <> t) do
  case Tuple <$> termParser v <*> typeParser t of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right (val /\ typ) -> do
      case runInference val of
        Left (err :: UnificationError) -> Assert.assert ("infer error: " <> show err) false
        Right suc ->
          case alphaEquivalent suc typ of
            Right b -> Assert.assert ("Expected to unify with: " <> prettyPrint suc) b
            Left err -> Assert.assert ("unification error: " <> prettyPrint suc <> " | " <> show err) false

testRun :: String -> GHalt -> TestSuite
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
    Right (val /\ typ) -> do
      case runInference val of
        Left (err :: UnificationError) -> Assert.assert ("infer error: " <> show err) false
        Right suc ->
          case alphaEquivalent suc typ of
            Right b -> Assert.assert ("Expected to unify with: " <> prettyPrint suc) b
            Left err -> Assert.assert ("unification error: " <> prettyPrint suc <> " | " <> show err) false



testExpectErr :: String -> UnificationError -> TestSuite
testExpectErr v e = test ("(" <> v <> ") :: _|_") do
  case termParser v of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right (val :: Term) -> do
      case runInference val of
        Left e' -> Assert.equal e e'
        Right (_ :: Term) -> Assert.assert "Expected failure but got success" false


alphaEquivalent :: Term -> Term -> Either UnificationError Boolean
alphaEquivalent t1 t2 = do
  a <- fst do
    runUnification do
       _ <- unify t2 t1
       x <- rewrite t2
       pure  (universe x == universe t1)
  b <- fst do
    runUnification do
       _ <- unify t1 t2
       x <- rewrite t1
       pure  (universe x == universe t2)
  pure (a && b)


typeParser :: String -> Either ParseError Term
typeParser s = runIndent $ runParserT s do
  v <- parseType
  eof
  pure v


termParser :: String -> Either ParseError Term
termParser s = runIndent $ runParserT s do
  v <- parseValue
  eof
  pure v


