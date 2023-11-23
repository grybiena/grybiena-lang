module Test.Term where

import Prelude

import Control.Comonad.Cofree (head)
import Control.Lazy (fix)
import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState)
import Data.Either (Either(..))
import Data.Functor.Mu (Mu)
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Language.Kernel.Effect (effectNatives)
import Language.Kernel.Pure (pureModule)
import Language.Lambda.Calculus (LambdaF(..))
import Language.Lambda.Inference (infer)
import Language.Lambda.Reduction (elimAbs, reduce)
import Language.Lambda.Unification (class Fresh, TypingContext, runUnificationT)
import Language.Native (Native(..))
import Language.Native.Meta (metaModule)
import Language.Native.Module (NativeModule, nativeModuleUnion)
import Language.Native.Reify (class Reify, nativeModule, reify)
import Language.Parser.Term (parser)
import Language.Term (TT(..), Term, UnificationError, Var)
import Matryoshka.Class.Recursive (project)
import Parsing (ParseError, ParserT, runParserT)
import Parsing.String (eof)
import Pretty.Printer (prettyPrint)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

testFix :: TestSuite
testFix = test "fix" $ do
  let foo :: Int -> Int
      foo i | i == 0 = 0
      foo i | i > 0 = foo (i-1)
      foo i = foo (i+1)
      foo' :: (Int -> Int) -> Int -> Int
      foo' _ i | i == 0 = 0
      foo' f i | i > 0 = f (i-1)
      foo' f i = f (i+1)
  Assert.equal (foo 10) ((fix foo') 10)
  Assert.equal (foo (-10)) ((fix foo') (-10))
  let a :: Int -> Int
      a i | i == 0 = 1
      a i | i > 0 = b i
      a i = a (i+3)
      b :: Int -> Int
      b i | i == 0 = 0
      b i | i < 0 = a i
      b i = b (i-2)
      a' :: ((Int -> Int) -> Int -> Int) -> (Int -> Int) -> Int -> Int
      a' _ _ i | i == 1 = 1
      a' _ f i | i > 0 = f i
      a' s f i = s f (i+3)
      b' :: (Int -> Int) -> Int -> Int
      b' _ i | i == 0 = 0
      b' s i | i < 0 = (fix a') s i
      b' s i = s (i-2)
      b'' :: Int -> Int
      b'' = fix b'
      a'' :: Int -> Int
      a'' = (fix a') b''
  Assert.equal (a 10) (a'' 10)
  Assert.equal (a (-10)) (a'' (-10))
  Assert.equal (b 10) (b'' 10)
  Assert.equal (b (-10)) (b'' (-10))








termTests :: Effect Unit
termTests = runTest do
  suite "Language.Void" do
    testFix

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

    testInferType "\\x -> let { i = 1 } in x i" "((Int -> t4) -> t4)"
    testInferType "\\x -> let { i = 1; j = 2 } in x i j" "((Int -> (Int -> t7)) -> t7)"
    testInferType "\\x -> let { i = \\a -> intPlus a 1 } in i x" "(Int -> Int)"
    testInferType "\\x -> let { i = 1; j = intPlus i 2 } in x i j" "((Int -> (Int -> t11)) -> t11)"
    testInferType "\\x -> let { j = intPlus i 2; i = 1 } in x i j" "((Int -> (Int -> t11)) -> t11)"
    testInferType "\\x -> let { i = intPlus j 1; j = 2 } in x i j" "((Int -> (Int -> t11)) -> t11)"

    testInferType "\\x -> let { i = intPlus j 1; j = intPlus i 2 } in x i j" "((Int -> (Int -> t15)) -> t15)"


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
    testInferType "1 :: Int :: *" "Int" 


    testInferKind "forall a . a" "(t2 -> t2)"
    testInferKind "forall a b. a b" "((t4 -> t6) -> (t4 -> t6))"
    testInferKind "forall a b. b a" "(t3 -> ((t3 -> t6) -> t6))" 
    testInferKind "forall a . a -> a" "(* -> *)"
    testInferKind "forall a b . a -> b" "(* -> (* -> *))"

    testInferKind "*" "**"
    testInferKind "* -> *" "*"

    testInferKind "* :: ** :: *** :: ****" "**"
    testInferKind "**" "***"

    testInferKind "Int" "*"
    testInferKind "Number" "*"

    -- Effect
    testInferType "pureEffect" "(forall t2 . (t2 -> (Effect t2)))"
    testInferSkiType "pureEffect" "(forall t2 . (t2 -> (Effect t2)))"

    testInferType "pureEffect @Int" "(Int -> (Effect Int))"
    testInferSkiType "pureEffect @Int" "(Int -> (Effect Int))"

    -- skolemizing removes the forall, encoding its scope into the type variables 
    testInferType "\\x -> pureEffect x" "(t3 -> (Effect t3))"
    -- This works by eta reduction
    testInferSkiType "\\x -> pureEffect x" "(forall t2 . (t2 -> (Effect t2)))"

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

    testInferType "pureEffect bindEffect" "(Effect (forall t5 . (forall t6 . ((Effect t5) -> ((t5 -> (Effect t6)) -> (Effect t6))))))"
    


    -- Compile
    testCompileEval "intPlus 1 1" (Assert.equal 2)
    testCompileEval "intPlus (intPlus 1 1) (intPlus 1 1)" (Assert.equal 4)
    testCompileEval "numPlus (numPlus 1.0 1.0) (numPlus 1.0 1.0)" (Assert.equal 4.0)
    testCompileEval "pureEffect (numPlus (numPlus 1.0 1.0) (numPlus 1.0 1.0))"
                    (\(out :: Effect Number) -> do
                        n <- liftEffect out
                        Assert.equal 4.0 n
                    )
    testCompileEval "\\x -> pureEffect (numPlus 1.0 x)"
                    (\(out :: Number -> Effect Number) -> do
                        n <- liftEffect (out 3.0)
                        Assert.equal 4.0 n
                    )

    testCompileEval "(\\x -> let { i = \\a -> intPlus a 1 } in i x) 1" (Assert.equal 2)

    testCompileEval "(\\x -> let { j = intPlus i 2; i = 1 } in x i j) intPlus" (Assert.equal 4)
    testCompileEval "(\\x -> let { i = intPlus j 2; j = 1 } in x j i) intPlus" (Assert.equal 4)





testInferType :: String -> String -> TestSuite
testInferType v t = test ("(" <> v <> ") :: " <> t) $ do
  e <- fst <$> runUnificationT do
    vt <- termParser v
    case vt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right (val :: Term) -> do
        (i :: Term) <- head <$> infer val
        liftAff $ Assert.equal t (prettyPrint i)
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false


testInferSkiType :: String -> String -> TestSuite
testInferSkiType v t = test ("(" <> v <> ") :: " <> t) $ do
  e <- fst <$> runUnificationT do
    vt <- termParser v
    case vt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right (val :: Term) -> do
        ski <- elimAbs val
--        liftEffect $ log $ prettyPrint ski
        (i :: Term) <- head <$> infer ski
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
      Right ((val :: Term) /\ (_ :: Term)) -> do
        (i :: Term) <- head <$> infer val
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
      Right ((val :: Term) /\ (_ :: Term)) -> do
        (i :: Term) <- head <$> infer val
        (j :: Term) <- head <$> infer i
        liftAff $ Assert.equal t (prettyPrint i)
        liftAff $ Assert.equal k (prettyPrint j)
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false

testCompileEval :: forall t. Reify t => String -> (t -> Aff Unit) -> TestSuite
testCompileEval v check = test v $ do
  e <- fst <$> runUnificationT do
    r <- compile v (Proxy :: Proxy t)
    case r of
      Left err -> liftAff $ Assert.assert (show err) false
      Right su -> liftAff $ check su
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Identity) -> Assert.assert ("infer error: " <> prettyPrint err) false



--testExpectErr :: String -> UnificationError Identity -> TestSuite
--testExpectErr v e = test ("(" <> v <> ") :: _|_") do
--  case termParser v of
--    Left err -> Assert.assert ("parse error: " <> show err) false
--    Right (val :: Term) -> do
--      case runInference val of
--        Left e' -> Assert.equal e e'
--        Right (_ :: Term) -> Assert.assert "Expected failure but got success" false

data CompileError =
    ReductionError String
  | TypeError String
  | ParseError ParseError

derive instance Generic CompileError _
instance Show CompileError where
  show = genericShow

compile :: forall t m.
           Reify t
        => MonadState (TypingContext Var Mu Var TT) m
        => MonadThrow (UnificationError Identity) m
        => Fresh Int m
        => MonadRec m
        => String -> Proxy t -> m (Either CompileError t) 
compile s ty = do
    t <- termParser s
    case t of
      Left err -> pure $ Left $ ParseError err
      Right val -> do
        out <- reduce val >>= elimAbs >>= reduce
        case project out of
          Cat (Native (Purescript { nativeType, nativeTerm })) -> do
            let tyt = reify ty
            if tyt == nativeType
              then pure $ Right $ unsafeCoerce nativeTerm
              else pure $ Left $ TypeError $ prettyPrint tyt <> " =?= " <> prettyPrint nativeType
          _ -> pure $ Left $ ReductionError $ prettyPrint out 




typeParser :: forall m. MonadState (TypingContext Var Mu Var TT) m => MonadRec m => String -> m (Either ParseError Term) 
typeParser s = runParserT s do
  let someKernel = nativeModuleUnion (nativeModule pureModule) (metaModule effectNatives)
  v <- (parser someKernel).parseType
  eof
  pure v


termParser :: forall m. MonadState (TypingContext Var Mu Var TT) m => MonadRec m => String -> m (Either ParseError Term)
termParser s = runParserT s do
  let mm :: NativeModule _ (ParserT String m (Native Term))
      mm = (metaModule effectNatives)
      someKernel = nativeModuleUnion (nativeModule pureModule) mm 
  v <- (parser someKernel).parseValue
  eof
  pure v


