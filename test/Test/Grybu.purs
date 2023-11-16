module Test.Grybu where

import Prelude

import Control.Comonad.Cofree (head)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff.Class (liftAff)
import Language.Grybu (Term, UnificationError, Var)
import Language.Lambda.Inference (infer)
import Language.Lambda.Reduction (elimAbs)
import Language.Lambda.Unification (class Fresh, runUnificationT)
import Language.Parser.Kernel (parseType, parseValue)
import Parsing (ParseError, runParserT)
import Parsing.String (eof)
import Pretty.Printer (prettyPrint)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

grybuTests :: Effect Unit
grybuTests = runTest do
  suite "Language.Void" do

--    testExpectErr "x" (NotInScope $ TermVar "x")
--
--    testExpectErr "\\x -> x x" $
--                  Err "An infinite type was inferred for an expression: (t2 -> t3) while trying to match type t2" 
--
--    testExpectErr "\\f -> (\\x -> f (x x)) (\\x -> f (x x))" $
--                  Err "An infinite type was inferred for an expression: (t3 -> t4) while trying to match type t3"

    -- I
    testInferType "\\x -> x" "(t1 -> t1)"
    testInferSkiType "\\x -> x" "(t1 -> t1)"

    -- K
    testInferType "\\x y -> x" "(t1 -> (t2 -> t1))"
    testInferSkiType "\\x y -> x" "(t1 -> (t2 -> t1))"


    testInferType "\\x y -> y" "(t1 -> (t2 -> t2))" 
    testInferSkiType "\\x y -> y" "(t2 -> (t3 -> t3))"
 

    -- eta reduction 
    testInferType "\\x y -> x y" "((t2 -> t4) -> (t2 -> t4))"
    testInferSkiType "\\x y -> x y" "(t1 -> t1)"

    testInferType "\\x y z -> x y z" "((t2 -> (t3 -> t7)) -> (t2 -> (t3 -> t7)))"
    testInferSkiType "\\x y z -> x y z" "(t1 -> t1)"

    testInferType "\\x y z a -> x y z a" "((t2 -> (t3 -> (t4 -> t10))) -> (t2 -> (t3 -> (t4 -> t10))))"
    testInferSkiType "\\x y z a -> x y z a" "(t1 -> t1)"

    testInferSkiType "\\x y z a -> x z y a" "((t5 -> (t4 -> t3)) -> (t4 -> (t5 -> t3)))"



    -- K
    testInferType "\\x y -> y x" "(t1 -> ((t1 -> t4) -> t4))"
    testInferSkiType "\\x y -> y x" "(t5 -> ((t5 -> t3) -> t3))"

    -- S
    testInferType "\\x y z -> (x z) (y z)" "((t3 -> (t7 -> t9)) -> ((t3 -> t7) -> (t3 -> t9)))"
    testInferType "\\x y z -> x z (y z)" "((t3 -> (t7 -> t9)) -> ((t3 -> t7) -> (t3 -> t9)))"
    testInferSkiType "\\x y z -> x z (y z)" "((t1 -> (t2 -> t3)) -> ((t1 -> t2) -> (t1 -> t3)))"


    testInferType "1" "Int"
    testInferType "1.0" "Number"

    testInferType "intPlus 1 1" "Int"
    testInferType "intPlus 1" "(Int -> Int)"
    testInferType "intPlus" "(Int -> (Int -> Int))"


    testInferType "\\a -> a :: Int" "(Int -> Int)"


    testInferType "1 :: Int" "Int" 
    testInferType "1 :: Int :: *" "(Int :: *)" 





    testInferKind "forall a . a" "(t2 -> t2)"
    testInferKind "forall a b. a b" "((t4 -> t6) -> (t4 -> t6))"
    testInferKind "forall a b. b a" "(t3 -> ((t3 -> t6) -> t6))" 
    testInferKind "forall a . a -> a" "(* -> *)"
    testInferKind "forall a b . a -> b" "(* -> (* -> *))"

    testInferKind "*" "**"
    testInferKind "* -> *" "*"

    testInferKind "* :: ** :: *** :: ****" "(** :: (*** :: ****))"
    testInferKind "**" "***"

    testInferKind "Int" "*"
    testInferKind "Number" "*"

--
----    testRun "1" (Native $ int 1)
----    testRun "1.0" (Native $ num 1.0)
----    testRun "intPlus 1 1" (Native $ int 2)
----    testRun "intPlus (intPlus 1 1) (intPlus 1 1)" (Native $ int 4)
----
----    testRun "numPlus 1.0 1.0" (Native $ num 2.0)
----
----    testRun "numPlus (numPlus 99.9 0.001) (numPlus 0.0004 0.0005)" (Native $ num 99.90190000000001)
--
----    testRun "intPlus (1 1)" (Native $ int 4)
-- 
--
---- Pure
    testInferType "pureEffect" "(forall t1 . (t1 -> (Effect t1)))"
    testInferSkiType "pureEffect" "(forall t1 . (t1 -> (Effect t1)))"

    testInferType "pureEffect @Int" "(Int -> (Effect Int))"
    testInferSkiType "pureEffect @Int" "(Int -> (Effect Int))"

    -- skolemizing removes the forall, encoding its scope into the type variables 
    testInferType "\\x -> pureEffect x" "(t2 -> (Effect t2))"
    -- This works by eta reduction
    testInferSkiType "\\x -> pureEffect x" "(forall t1 . (t1 -> (Effect t1)))"

    -- application to a term with a concrete type infers the universally quantified type variable
    testInferType "(\\x -> pureEffect x) 1" "(Effect Int)"
    testInferSkiType "(\\x -> pureEffect x) 1" "(Effect Int)"

    -- application to a type annotation can be used to explicitly infer the type 
    testInferType "(\\x -> pureEffect @Int x) 1" "(Effect Int)"
    testInferSkiType "(\\x -> pureEffect @Int x) 1" "(Effect Int)"



    testInferType "bindEffect @Int @Int"  "((Effect Int) -> ((Int -> (Effect Int)) -> (Effect Int)))"
    testInferSkiType "bindEffect @Int @Int"  "((Effect Int) -> ((Int -> (Effect Int)) -> (Effect Int)))"

    testInferType "\\x y -> bindEffect @Int @Int y x" "((Int -> (Effect Int)) -> ((Effect Int) -> (Effect Int)))"
    testInferSkiType "\\x y -> bindEffect @Int @Int y x" "((Int -> (Effect Int)) -> ((Effect Int) -> (Effect Int)))"

    testInferType "\\x y -> bindEffect @Int @Int y x" "((Int -> (Effect Int)) -> ((Effect Int) -> (Effect Int)))"
    testInferSkiType "\\x y -> bindEffect @Int @Int y x" "((Int -> (Effect Int)) -> ((Effect Int) -> (Effect Int)))"

    testInferType "pureEffect bindEffect" "(Effect (forall t2 . (forall t3 . ((Effect t2) -> ((t2 -> (Effect t3)) -> (Effect t3))))))" 




--    testInferSkiType "\\x y -> bindEffect @Int x y" "((Effect Int) -> (t4 -> ((Int -> ( Effect x )) -> ( Effect x ))))"
--
--
--
--
--    testInferTypeThenKind "pureEffect @Int" "Int -> Effect Int" "*"


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



---- Bind
--    testInferType "bindEffect" "forall b a. Effect a -> (a -> Effect b) -> Effect b"
--    testInferType "bindEffect" "forall a b. Effect a -> (a -> Effect b) -> Effect b"
--
--
--    -- TODO this should fail
--    testInferType "bindEffect" "forall x y. Effect a -> (a -> Effect b) -> Effect b"
--
--    -- TODO this should pass
--    testInferTypeThenKind "\\x -> x" "a -> a"
--
--    -- TODO this is fails correctly
--    testInferTypeThenKind "pureEffect 1" "Int -> Effect Int"

testInferType :: String -> String -> TestSuite
testInferType v t = test ("(" <> v <> ") :: " <> t) $ do
  e <- fst <$> runUnificationT do
    vt <- termParser v
    tt <- typeParser t
    case Tuple <$> vt <*> tt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right ((val :: Term Identity) /\ (_ :: Term Identity)) -> do
        (i :: Term Identity) <- head <$> infer val
        liftAff $ Assert.equal t (prettyPrint i)
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false


testInferSkiType :: String -> String -> TestSuite
testInferSkiType v t = test ("(" <> v <> ") :: " <> t) $ do
  e <- fst <$> runUnificationT do
    vt <- termParser v
    tt <- typeParser t
    case Tuple <$> vt <*> tt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right ((val :: Term Identity) /\ (_ :: Term Identity)) -> do
        ski <- elimAbs val
--        liftEffect $ log $ prettyPrint ski
        (i :: Term Identity) <- head <$> infer ski
        liftAff $ Assert.equal t (prettyPrint i)
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false

testInferKind :: String -> String -> TestSuite
testInferKind v t = test ("(" <> v <> ") :: " <> t) $ do
  e <- fst <$> runUnificationT do
    vt <- typeParser v
    tt <- typeParser t
    case Tuple <$> vt <*> tt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right ((val :: Term Identity) /\ (_ :: Term Identity)) -> do
        (i :: Term Identity) <- head <$> infer val
        liftAff $ Assert.equal t (prettyPrint i)
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false

testInferTypeThenKind :: String -> String -> String -> TestSuite
testInferTypeThenKind v t k = test ("(" <> v <> ") :: " <> t) $ do
  e <- fst <$> runUnificationT do
    vt <- termParser v
    tt <- typeParser t
    case Tuple <$> vt <*> tt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right ((val :: Term Identity) /\ (_ :: Term Identity)) -> do
        (i :: Term Identity) <- head <$> infer val
        (j :: Term Identity) <- head <$> infer i
        liftAff $ Assert.equal t (prettyPrint i)
        liftAff $ Assert.equal k (prettyPrint j)
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false


--testExpectErr :: String -> UnificationError Identity -> TestSuite
--testExpectErr v e = test ("(" <> v <> ") :: _|_") do
--  case termParser v of
--    Left err -> Assert.assert ("parse error: " <> show err) false
--    Right (val :: Term Identity) -> do
--      case runInference val of
--        Left e' -> Assert.equal e e'
--        Right (_ :: Term Identity) -> Assert.assert "Expected failure but got success" false



typeParser :: forall m n. Monad n => Fresh Int m => MonadRec m => String -> m (Either ParseError (Term n)) 
typeParser s = runParserT s do
  v <- parseType
  eof
  pure v


termParser :: forall m n. Monad n => Fresh Int m => Fresh Var m => MonadRec m => String -> m (Either ParseError (Term n))
termParser s = runParserT s do
  v <- parseValue
  eof
  pure v


