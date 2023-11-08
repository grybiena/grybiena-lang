module Test.Main where

import Prelude

import Data.Either (Either(..))
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Language.Lambda.Inference (runInference)
import Language.Lambda.Unification (rewrite, runUnification, unify)
import Language.Void.Kind (Kind', KindUnificationError, parseKind)
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

    testInferKind "forall a . a" "k -> k"
    testInferKind "forall a b. a b" "(k -> j) -> (k -> j)" 
    testInferKind "forall a b. b a" "k -> (k -> j) -> j" 
    testInferKind "forall a . a -> a" "* -> *"
    testInferKind "forall a b . a -> b" "* -> * -> *"

-- kind inference (kind of)
-- 
-- we are treating universal quantification as a higher kinded type
-- which is a bit non-standard but makes some kind of sense
-- the forall a . e is interpreted as a lambda at the type level
-- 
-- e.g. haskell and purescript say that (forall a. a -> a :: Type)
-- 
-- but we say that (forall a. a -> a :: Type -> Type)
-- 
-- since you can only get the concrete `Type` of the function
-- after removing the universal quantification by applying a concrete `Type` for `a`
-- 
-- another way of looking at this is by applying more granular Kind annotations
--
-- (forall (a :: Type) . (a -> a :: Type)) :: Type -> Type
--
-- so what we have is more akin to the implicit arguments of idris 
-- where we might write the same thing as
--
-- { a :: Type } -> a -> a

-- indicating that we must first (implicitly) apply a Type for `a`
-- in order to get our hands on a value of type (a -> a) for that
-- specific Type.


--
-- when we have constraints on the type these act like guards 
-- that prevent the type lambda from being applied to a type that
-- does not satisfy the constraint
-- e.g. incrementByOne can only be applied to an `a` that is Numeric
-- incrementByOne :: forall a. Numeric a => a -> a
--






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


testInferKind :: String -> String -> TestSuite
testInferKind v t = test (v <> " :: " <> t) do
  case Tuple <$> typeParser v <*> kindParser t of
    Left err -> Assert.assert ("parse error: " <> show err) false
    Right (val /\ typ) -> do
      case runInference val of
        Left (err :: KindUnificationError) -> Assert.assert ("infer error: " <> show err) false
        Right suc ->
          case kalphaEquivalent suc typ of
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
 


kalphaEquivalent :: Kind' -> Kind' -> Either KindUnificationError Boolean
kalphaEquivalent t1 t2 = do
  a <- fst do
    runUnification do
       _ <- unify t2 t1
       x <- rewrite t2
       pure  (x == t1)
  b <- fst do
    runUnification do
       _ <- unify t1 t2
       x <- rewrite t1
       pure  (x == t2)
  pure (a && b)
      
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

kindParser :: String -> Either ParseError Kind' 
kindParser s = runIndent $ runParserT s do
  v <- parseKind
  eof
  pure v


