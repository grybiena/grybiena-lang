module Test.Main where

import Prelude

import Data.Either (Either(..))
import Data.Functor.Mu (Mu(..))
import Data.Traversable (traverse_)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Language.Lambda.Calculus (LambdaF(..))
import Language.Lambda.Infer (judgement)
import Language.Void.Type (Judgement, JudgementF(..), Type', runInfer, runInfer')
import Language.Void.Value (Value, parseValue)
import Matryoshka.Class.Recursive (project)
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
    unfurl "\\a b -> a b" 

tests :: Effect Unit
tests = runTest do
  suite "Language.Void" do
    testInferType "a" "t0"
    testInferType "\\a -> a" "t0 -> t0"
    testInferType "\\a b -> a" "t0 -> t1 -> t0"
    testInferType "\\a b -> b" "t0 -> t1 -> t1"
    testInferType "\\a b -> a b" "(t0 -> t1) -> t0 -> t1"
    testInferType "\\a b -> b a" "t0 -> (t0 -> t1) -> t1"

unfurl :: String -> TestSuite
unfurl v = test v do
  case valueParser v of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right suc -> do
      Assert.equal (Right suc) (valueParser $ prettyPrint suc)
      case runInfer' suc of
        Left err /\ _-> Assert.assert ("type error: " <> show err) false
        Right _ /\ j -> 
          liftEffect $ traverse_ (\x -> logUnfurl x *> log "------") j
 
logUnfurl :: Judgement -> Effect Unit
logUnfurl j = do
  let (ex :: Value) /\ (t :: Type') = judgement j
  log (prettyPrint ex <> " :: " <> prettyPrint t)
  case project j of
    HasType _ _ -> pure unit
    JudgeApp x y _ -> do
      logUnfurl x
      logUnfurl y
    JudgeAbs _ a _ -> do
      logUnfurl a


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




