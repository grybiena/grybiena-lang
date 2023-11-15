module Test.Grybu where

import Prelude

import Control.Comonad.Cofree ((:<))
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class (liftEffect)
import Language.Grybu (Native(..), TT(..), Term, UnificationError(..), Var(..), int, num, parseType, parseValue)
import Language.Lambda.Calculus (universe)
import Language.Lambda.Inference (runInference)
import Language.Lambda.Unification (rewrite, runUnification, unify)
import Machine.Closure (closure)
import Machine.Krivine (runUnbounded)
import Parsing (ParseError, runParserT)
import Parsing.Indent (runIndent)
import Parsing.String (eof)
import Pretty.Printer (prettyPrint)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)
import Unsafe.Coerce (unsafeCoerce)

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


--    testRunEffectInt "pureEffect @Int 1" 1
--
--    testRunEffectInt "bindEffect @Int @Int (pureEffect @Int 1) (pureEffect @Int)" 1
-- 
--    testRunEffectInt "bindEffect @Int @Int (pureEffect @Int 1) (\\a -> pureEffect @Int a)" 1

--    testRun "bindEffect @Int @Int (pureEffect @Int 1) (\\z -> bindEffect @Int @Int (pureEffect @Int (intPlus z 1)) (\\b -> pureEffect @Int (intPlus b 1)))" (Native $ int 3)
--    testInferType "bindEffect @Int @Int (pureEffect @Int 1) (\\z -> bindEffect @Int @Int (pureEffect @Int (intPlus z 1)) (\\b -> pureEffect @Int (intPlus b 1)))" "Effect Int"
--
--
--    testRun "bindEffect @Int @Int (bindEffect @Int @Int (pureEffect @Int 1) (\\a -> pureEffect @Int (intPlus a 1))) (\\b -> pureEffect @Int (intPlus b 1))" (Native $ int 3)
--    testInferType "bindEffect @Int @Int (bindEffect @Int @Int (pureEffect @Int 1) (\\a -> pureEffect @Int (intPlus a 1))) (\\b -> pureEffect @Int (intPlus b 1))" "Effect Int"



-- Bind
    testInferType "bindEffect" "forall b a. Effect a -> (a -> Effect b) -> Effect b"
    testInferType "bindEffect" "forall a b. Effect a -> (a -> Effect b) -> Effect b"


    -- TODO this should fail
    testInferType "bindEffect" "forall x y. Effect a -> (a -> Effect b) -> Effect b"

--    -- TODO this should pass
--    testInferTypeThenKind "\\x -> x" "a -> a"
--
--    -- TODO this is fails correctly
--    testInferTypeThenKind "pureEffect 1" "Int -> Effect Int"

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
      t <- runUnbounded (closure val Map.empty :< Nothing)
      case t of
        res | res == h -> pure unit
        res -> Assert.assert (show res <> " /= " <> show h) false

testRunEffectInt :: String -> Int -> TestSuite
testRunEffectInt v h = test ("run (" <> v <> ")") do
  case termParser v of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right (val :: Term Effect) -> do
       t <- runUnbounded (closure val Map.empty :< Nothing)
       case (t :: TT Effect Void) of
         Native (Purescript { nativeTerm }) -> do
           i <- liftEffect $ (unsafeCoerce nativeTerm :: Effect Int)
           Assert.equal h i
         e -> Assert.assert (show e) false
 
 

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


