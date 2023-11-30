module Test.Term where

import Prelude

import Control.Comonad.Cofree (head)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Except (runExceptT)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState)
import Data.Either (Either(..))
import Data.Functor.Mu (Mu)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Language.Kernel.Effect (effectNatives)
import Language.Kernel.Pure (pureModule)
import Language.Lambda.Calculus (LambdaF(..))
import Language.Lambda.Inference (infer)
import Language.Lambda.Reduction (elimAbs, reduce)
import Language.Lambda.Unification (class Fresh, TypingContext, runUnificationT)
import Language.Lambda.Unification.Error (UnificationError)
import Language.Native (Native(..))
import Language.Native.Module (NativeModule, nativeModuleUnion)
import Language.Native.Reify (class Reify, nativeModule, reify)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Basis (runStringParserT)
import Language.Parser.Term (Parser(..), parser)
import Language.Term (TT(..), Term, Var)
import Matryoshka.Class.Recursive (project)
import Parsing (ParseError, ParserT)
import Parsing.String (eof)
import Pretty.Printer (prettyPrint)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)


termTests :: Effect Unit
termTests = runTest do
  suite "Language.Void" do

--    testExpectErr "x" (NotInScope $ TermVar "x")
--
--    testExpectErr "\\x -> x x" $
--                  Err "An infinite type was inferred for an expression: (t2 -> t3) while trying to match type t2" 
--
--    testExpectErr "\\f -> (\\x -> f (x x)) (\\x -> f (x x))" $
--                  Err "An infinite type was inferred for an expression: (t3 -> t4) while trying to match type t3"


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
    

    -- Compile
    testCompileEval "intPlus 1 1" (Assert.equal 2)
    testCompileEval "intPlus (intPlus 1 1) (intPlus 1 1)" (Assert.equal 4)
    testCompileEval "numPlus (numPlus 1.0 1.0) (numPlus 1.0 1.0)" (Assert.equal 4.0)
    testCompileEval "pureEffect (numPlus (numPlus 1.0 1.0) (numPlus 1.0 1.0))"
                    (\(out :: Effect Number) -> do
                        n <- liftEffect out
                        Assert.equal 4.0 n
                    )

    testCompileEval "pureEffect @Number (numPlus (numPlus 1.0 1.0) (numPlus 1.0 1.0))"
                    (\(out :: Effect Number) -> do
                        n <- liftEffect out
                        Assert.equal 4.0 n
                    )

    testCompileEval "\\x -> pureEffect (numPlus 1.0 x)"
                    (\(out :: Number -> Effect Number) -> do
                        n <- liftEffect (out 3.0)
                        Assert.equal 4.0 n
                    )


    testCompileEval "\\x -> pureEffect @Number (numPlus 1.0 x)"
                    (\(out :: Number -> Effect Number) -> do
                        n <- liftEffect (out 3.0)
                        Assert.equal 4.0 n
                    )


    testCompileEval "\\x -> pureEffect @Number (numPlus 1.0 x)"
                    (\(out :: Number -> Effect Number) -> do
                        n <- liftEffect (out 3.0)
                        Assert.equal 4.0 n
                    )

    testCompileEval "(\\x -> let { i = \\a -> intPlus a 1 } in i x) 1" (Assert.equal 2)

    testCompileEval "(\\x -> let { j = intPlus i 2; i = 1 } in x i j) intPlus" (Assert.equal 4)
    testCompileEval "(\\x -> let { i = intPlus j 2; j = 1 } in x j i) intPlus" (Assert.equal 4)

    testCompileEval "(\\x -> if x then 1 else 0) true" (Assert.equal 1)
    testCompileEval "(\\x -> if x then 1 else 0) false" (Assert.equal 0)

    testCompileEval "(\\x -> if intGt x 0 then 1 else 0) 5" (Assert.equal 1)
    testCompileEval "(\\x -> if intGt x 0 then 1 else 0) (-5)" (Assert.equal 0)





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
    Left (err :: UnificationError Mu Var TT) -> Assert.assert ("infer error: " <> prettyPrint err) false


testInferSkiType :: String -> String -> TestSuite
testInferSkiType v t = test ("(" <> v <> ") :: " <> t) $ do
  e <- fst <$> runUnificationT do
    vt <- termParser v
    case vt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right (val :: Term) -> do
        ski <- runExceptT $ elimAbs (Proxy :: Proxy Parser) val
        case ski of
          Left err -> liftAff $ Assert.assert ("basis error: " <> show err) false    
          Right su -> do

    --        liftEffect $ log $ prettyPrint ski
    --        liftEffect $ log $ show ski
            (i :: Term) <- head <$> infer su
            liftAff $ Assert.equal t (prettyPrint i)
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Mu Var TT) -> Assert.assert ("infer error: " <> prettyPrint err) false

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
    Left (err :: UnificationError Mu Var TT) -> Assert.assert ("infer error: " <> prettyPrint err) false

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
    Left (err :: UnificationError Mu Var TT) -> Assert.assert ("infer error: " <> prettyPrint err) false

testCompileEval :: forall t. Reify t => String -> (t -> Aff Unit) -> TestSuite
testCompileEval v check = test v $ do
  e <- fst <$> runUnificationT do
    r <- compile v (Proxy :: Proxy t)
    case r of
      Left err -> liftAff $ Assert.assert (show err) false
      Right su -> liftAff $ check su
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Mu Var TT) -> Assert.assert ("infer error: " <> prettyPrint err) false



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
  | BasisError ParseError
  | UnifError (UnificationError Mu Var TT)

derive instance Generic CompileError _
instance Show CompileError where
  show = genericShow

compile :: forall t m.
           Reify t
        => MonadState (TypingContext Var Mu Var TT) m
        => MonadThrow (UnificationError Mu Var TT) m
        => Fresh Int m
        => MonadRec m
        => MonadEffect m
        => String -> Proxy t -> m (Either CompileError t) 
compile s ty = do
    t <- termParser s
    case t of
      Left err -> pure $ Left $ ParseError err
      Right val -> do
        let reductionStep v = do 
              q <- runExceptT $ runExceptT $ reduce v
              case q of
                Left err -> throwError $ UnifError err 
                Right (Left err) -> throwError $ ParseError err
                Right (Right u) -> do
--                  liftEffect $ log $ prettyPrint u
                  pure u
        let eliminationStep v = do 
              let p = (Proxy :: Proxy Parser)
              q <- runExceptT $ runExceptT $ elimAbs p v
              case q of
                Left err -> throwError $ UnifError err 
                Right (Left err) -> throwError $ ParseError err
                Right (Right u) -> do
--                  liftEffect $ log $ prettyPrint u
                  pure u


        out' <- runExceptT do
           i <- reductionStep val >>= eliminationStep
           j <- reductionStep i >>= eliminationStep
           reductionStep j >>= eliminationStep


--           pure k



        case out' of
          Left err -> pure $ Left err 
          Right out -> do            
            case project out of
              Cat (Native (Purescript { nativeType, nativeTerm })) -> do
                let tyt = reify ty
                if prettyPrint tyt == prettyPrint nativeType
                  then pure $ Right $ unsafeCoerce nativeTerm
                  else pure $ Left $ TypeError $ prettyPrint tyt <> " =?= " <> prettyPrint nativeType
              _ -> pure $ Left $ ReductionError $ show out 
        
    


typeParser :: forall m. MonadState (TypingContext Var Mu Var TT) m => MonadRec m => String -> m (Either ParseError Term) 
typeParser s = runStringParserT s do
  let someKernel = nativeModuleUnion (nativeModule pureModule) (unsafeModule (Proxy :: Proxy Parser) effectNatives)
  v <- (parser someKernel).parseType
  Parser eof
  pure v


termParser :: forall m. MonadState (TypingContext Var Mu Var TT) m => MonadRec m => String -> m (Either ParseError Term)
termParser s = runStringParserT s do
  let mm :: NativeModule _ (ParserT String m (Native Term))
      mm = (unsafeModule (Proxy :: Proxy Parser) effectNatives)
      someKernel = nativeModuleUnion (nativeModule pureModule) mm 
  v <- (parser someKernel).parseValue
  Parser eof
  pure v




