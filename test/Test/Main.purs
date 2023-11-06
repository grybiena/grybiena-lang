module Test.Main where

import Prelude

import Control.Comonad.Cofree ((:<))
import Data.Either (Either(..))
import Data.List (List(..), singleton, (:))
import Data.Maybe (maybe)
import Data.Tree (Tree, drawTree, drawTreeLines)
import Data.Tree.Zipper (fromTree, insertAfter, insertChild, toTree)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Language.Lambda.Calculus (abs, app)
import Language.Lambda.Infer (judgement)
import Language.Void.Type (Judgement, JudgementF(..), Type', runInfer, runInfer')
import Language.Void.Value (ValVar(..), Value, parseValue)
import Matryoshka.Class.Recursive (project)
import Parsing (ParseError, runParserT)
import Parsing.Indent (runIndent)
import Parsing.String (eof)
import Pretty.Printer (prettyPrint)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

main :: Effect Unit
main = do
  runTest do
    suite "Language.Void" do
      unfurl "\\a b -> a b a" 
  tests

tests :: Effect Unit
tests = runTest do
  suite "Language.Void" do
--    testInferType "a" "t0"
    testInferType "\\a -> a" "(t0 -> t0)"
    testInferType "\\a b -> a" "(t0 -> (t1 -> t0))"
    testInferType "\\a b -> b" "(t0 -> (t1 -> t1))"
    testInferType "\\a b -> a b" "((t1 -> t3) -> (t1 -> t3))"
    testInferType "\\a b -> b a" "(t0 -> ((t0 -> t3) -> t3))"

unfurl :: String -> TestSuite
unfurl v = test v do
  case valueParser v of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right suc -> do
      Assert.equal (Right suc) (valueParser $ prettyPrint suc)
      case runInfer' suc of
        Left err /\ _-> Assert.assert ("type error: " <> show err) false
        Right t /\ j -> do 
          liftEffect $ log $ drawTree $ tTree t
          liftEffect $ log $ drawTreeLines $ (maybe (singleton ".") showUnfurl) <$> j
 
tTree :: Judgement -> Tree String
tTree j =
  case project j of
      HasType (ValVar v) t -> (v <> " :: " <> prettyPrint t) :< Nil
      JudgeApp x y t ->
        let (exx :: Value) /\ (_ :: Type') = judgement $ project x
            (exy :: Value) /\ (_ :: Type') = judgement $ project y
            sx =  prettyPrint (app exx exy) <> " :: " <> prettyPrint t
         in toTree $ insertAfter (tTree y) $ insertChild (tTree x) (fromTree (sx :< Nil))
      JudgeAbs v a t ->
        let (ex :: Value) /\ (_ :: Type') = judgement $ project a
            sx =  prettyPrint (abs v ex) <> " :: " <> prettyPrint t
         in toTree $ insertChild (tTree a) (fromTree (sx :< Nil)) 




 
showUnfurl :: Judgement -> List String
showUnfurl j = 
  let (ex :: Value) /\ (t :: Type') = judgement $ project j
      h = prettyPrint ex <> " :: " <> prettyPrint t
  in case project j of
       HasType _ _ -> singleton h
       JudgeApp x y _ -> h:(showUnfurl x <> showUnfurl y)
       JudgeAbs _ a _ -> h:(showUnfurl a)


logUnfurl :: Judgement -> Effect Unit
logUnfurl j = do
  let (ex :: Value) /\ (t :: Type') = judgement $ project j
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




