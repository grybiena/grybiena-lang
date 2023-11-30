module Test.Runner where

import Prelude

import Control.Comonad.Cofree (head)
import Data.Array (catMaybes, elem, nub, (!!))
import Data.Either (Either(..))
import Data.Functor.Mu (Mu)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.Traversable (sequence_, traverse)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Language.Lambda.Inference (infer)
import Language.Lambda.Unification (rewrite, runUnificationT, unify)
import Language.Lambda.Unification.Error (UnificationError)
import Language.Term (TT, Term, Var)
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile, readdir)
import Pretty.Printer (prettyPrint)
import Test.Term (termParser, typeParser)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

data TypeTest = TypeTest String String
instance Show TypeTest where
  show (TypeTest te ty) = "TypeTest " <> te <> " " <> ty



findTypeTests :: String -> Array String -> Array TypeTest
findTypeTests dir a =
  let z = split (Pattern ".") <$> a
      x = nub $ catMaybes ((\l -> l!!0) <$> z)
      f o = 
        let te = o <> ".term"
            ty = o <> ".type"
         in if (te `elem` a) && (ty `elem` a)
              then Just $ TypeTest (dir <> "/" <> te)  (dir <> "/" <> ty)
              else Nothing
   in catMaybes (f <$> x) 

buildTypeTest :: TypeTest -> Effect TestSuite
buildTypeTest (TypeTest te ty) = testInferType <$> (readTextFile UTF8 te) <*> (readTextFile UTF8 ty)

typeTestSuite :: String -> Effect Unit
typeTestSuite dir = do
  ls <- readdir dir
  ts <- traverse buildTypeTest (findTypeTests dir ls)
  runTest $ suite dir $ sequence_ ts

testInferType :: String -> String -> TestSuite
testInferType v t = test (v <> "  :: " <> t) $ do
  e <- fst <$> runUnificationT do
    vt <- termParser v
    tt <- typeParser t
    case Tuple <$> vt <*> tt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right ((val :: Term) /\ (ty :: Term)) -> do
        (i :: Term) <- head <$> infer val
        e <- liftAff $ structurallyEquivalent i ty
        liftAff $ Assert.assert t e
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Mu Var TT) -> Assert.assert ("infer error: " <> prettyPrint err) false


structurallyEquivalent :: Term -> Term -> Aff Boolean
structurallyEquivalent a b = do
  let check (Right x) = pure x
      check (Left (_ :: UnificationError Mu Var TT)) = pure false
  check =<< fst <$> runUnificationT do
     unify b a
     ar <- rewrite a
     br <- rewrite b
     pure (ar == br)






