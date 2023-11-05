module Test.Main where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Language.Void.Type (runInfer)
import Language.Void.Value (Value, parseValue)
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
--    testInferType "a" "t0"
    testInferType "\\a -> a" "t0 -> t0"
    testInferType "\\a b -> a" "t0 -> t1 -> t0"
    testInferType "\\a b -> b" "t0 -> t1 -> t1"
    testInferType "\\a b -> a b" "(t0 -> t1) -> t0 -> t1"
--    testInferType "\\a b -> b a" "t0 -> (t0 -> t1) -> t1"




testInferType :: String -> String -> TestSuite
testInferType v t = test (v <> " :: " <> t) do
  case valueParser v of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right suc -> do
      Assert.equal (Right suc) (valueParser $ prettyPrint suc)
      case runInfer suc of
        Left err -> Assert.assert ("type error: " <> show err) false
        Right suct -> Assert.equal t (prettyPrint suct)
 
      

valueParser :: String -> Either ParseError Value
valueParser s = runIndent $ runParserT s do
  v <- parseValue
  eof
  pure v




