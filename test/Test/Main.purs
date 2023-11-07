module Test.Main where

import Prelude

import Data.Either (Either(..))
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Language.Lambda.Inference (runInference)
import Language.Lambda.Unification (rewrite, runUnification, unify)
import Language.Void.Type (Type', UnificationError(..), parseType)
import Language.Void.Value (ValVar(..), Value, parseValue)
import Parsing (ParseError, runParserT)
import Parsing.Indent (runIndent)
import Parsing.String (eof)
import Pretty.Printer (prettyPrint)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

main :: Effect Unit
main = runTest do
  suite "Language.Void" do

    testExpectErr "x" (NotInScope $ ValVar "x")

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



testInferType :: String -> String -> TestSuite
testInferType v t = test (v <> " :: " <> t) do
  case Tuple <$> valueParser v <*> typeParser t of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right (val /\ typ) -> do
      case runInference val of
        Left (err :: UnificationError) -> Assert.assert ("infer error: " <> show err) false
        Right suc ->
          case alphaEquivalent suc typ of
            Right b -> Assert.assert ("Expected to unify with: " <> prettyPrint suc) b
            Left err -> Assert.assert ("unification error: " <> prettyPrint suc <> " | " <> show err) false


testExpectErr :: String -> UnificationError -> TestSuite
testExpectErr v e = test (v <> " :: _|_") do
  case valueParser v of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right (val :: Value) -> do
      case runInference val of
        Left e' -> Assert.equal e e'
        Right (_ :: Type') -> Assert.assert "Expected failure but got success" false

data Fixture =
    ExpectError { term :: String, err :: UnificationError }
  | ExpectInfer { term :: String, typ :: String }
 


alphaEquivalent :: Type' -> Type' -> Either UnificationError Boolean
alphaEquivalent t1 t2 = fst do
    runUnification do
       _ <- unify t2 t1
       x <- rewrite t2
       pure  (x == t1)
      

valueParser :: String -> Either ParseError Value
valueParser s = runIndent $ runParserT s do
  v <- parseValue
  eof
  pure v


typeParser :: String -> Either ParseError Type' 
typeParser s = runIndent $ runParserT s do
  v <- parseType
  eof
  pure v


