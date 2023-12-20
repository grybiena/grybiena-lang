module Test.Functor.Type where

import Prelude

import Control.Comonad.Cofree (Cofree, head)
import Control.Monad.Except (runExceptT)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (runStateT)
import Data.Either (Either(..))
import Data.FoldableWithIndex (traverseWithIndex_)
import Data.Functor.Mu (Mu)
import Data.Traversable (traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class.Console (log, logShow)
import Language.Category.App (App)
import Language.Category.Arrow (Arrow)
import Language.Category.Forall (Forall)
import Language.Category.Hole (Hole)
import Language.Category.Level (Level)
import Language.Category.Var (class Fresh, Var)
import Language.Functor.Coproduct (type (:+:))
import Language.Functor.Elimination (class Eliminated)
import Language.Functor.Parse (parser)
import Language.Functor.Reduction (infer, reduce, reduceFix, reduceFixU)
import Language.Functor.Universe (Universe, flatten)
import Language.Monad.Context (class Context, Ctx(..), emptyCtx)
import Matryoshka (embed, project)
import Parsing (ParseError, runParserT)

foofa :: Effect Unit
foofa = do

  goo <- parseFoo "forall a . a b c"
  logShow goo

  foo <- parseFoo "forall a . forall b . a b"
  logShow foo
  case foo of
    Left _ -> pure unit
    Right fo -> do
       (i /\ ctx) <- flip runStateT (emptyCtx :: Ctx Var (Universe Mu Foo)) $ runExceptT $ infero fo >>= traverse reduca 
       case i of
         Left (_ :: String) -> pure unit
         Right t -> do
            showCtx ctx
            logShow $ flatten $ head t 
            (z /\ ctx2) <- flip runStateT ctx $ reduca $ head t
            showCtx ctx2
            logShow $ flatten z
            

  pure unit

showCtx :: Ctx Var (Universe Mu Foo) -> Effect Unit
showCtx (Ctx c) = traverseWithIndex_ showAssumption c.ctx
  where showAssumption k v = log $ show k <> " :: " <> show (flatten v)

type Foo = (Var :+: Hole :+: Level :+: Arrow :+: Forall :+: App)

parseFoo :: forall m . MonadRec m => String -> m (Either ParseError (Mu Foo))
parseFoo s = runParserT s (embed <$> parser)


 
infero :: forall m.
          MonadRec m
       => Context Var (Universe Mu Foo) m 
       => Fresh m
       => Mu Foo -> m (Cofree Foo (Universe Mu Foo))
infero = infer

--type Bar = Forall :+: App :+: Var

reduco :: forall m.
          MonadRec m
       => Eliminated m 
       => Cofree Foo (Universe Mu Foo) -> m (Cofree Foo (Universe Mu Foo))
reduco = reduceFixU

reduca :: forall m.
          MonadRec m
       => Fresh m
       => Eliminated m
       => Universe Mu Foo -> m (Universe Mu Foo)
reduca = map embed <<< reduco <<< project

