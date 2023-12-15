module Test.Type.Infer where

import Prelude

import Control.Comonad.Cofree (head)
import Control.Monad.RWS (RWSResult(..))
import Data.Array (catMaybes, elem, nub, (!!))
import Data.Either (Either(..))
import Data.Functor.Mu (Mu)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.Traversable (sequence_, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff.Class (liftAff)
import Language.Lambda.Inference (infer)
import Language.Lambda.Unification (runUnificationT)
import Language.Lambda.Unification.Error (UnificationError)
import Language.Term (TT, Term, Var)
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile, readdir)
import Pretty.Printer (prettyPrint)
import Test.Term (typeParser)
import Test.Term.Infer (structurallyEquivalent)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert as Assert
import Test.Unit.Main (runTest)

inferKindSuite :: Effect Unit
inferKindSuite = do
  let dir = "fixtures/type/infer"
  ls <- readdir dir
  ts <- traverse buildInferTest (findInferTests dir ls)
  runTest $ suite dir $ sequence_ ts



data InferTest = InferTest String String
instance Show InferTest where
  show (InferTest te ty) = "InferTest " <> te <> " " <> ty

findInferTests :: String -> Array String -> Array InferTest
findInferTests dir a =
  let z = split (Pattern ".") <$> a
      x = nub $ catMaybes ((\l -> l!!0) <$> z)
      f o = 
        let te = o <> ".type"
            ty = o <> ".kind"
         in if (te `elem` a) && (ty `elem` a)
              then Just $ InferTest (dir <> "/" <> te)  (dir <> "/" <> ty)
              else Nothing
   in catMaybes (f <$> x) 

buildInferTest :: InferTest -> Effect TestSuite
buildInferTest (InferTest te ty) = testInferKind te <$> (readTextFile UTF8 te) <*> (readTextFile UTF8 ty)

testInferKind :: String -> String -> String -> TestSuite
testInferKind nm v t = test nm do
  RWSResult _ e _ <- runUnificationT do
    vt <- typeParser v
    tt <- typeParser t
    case Tuple <$> vt <*> tt of
      Left err -> liftAff $ Assert.assert ("parse error: " <> show err) false    
      Right ((val :: Term) /\ (ty :: Term)) -> do
        (i :: Term) <- head <$> infer val
        e <- liftAff $ structurallyEquivalent i ty
        liftAff $ Assert.assert (prettyPrint i <> " =?= " <> prettyPrint ty) e
  case e of
    Right _ -> pure unit
    Left (err :: UnificationError Mu Var TT) -> Assert.assert ("infer error: " <> prettyPrint err) false

