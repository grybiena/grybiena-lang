module Test.Functor.Type where

import Prelude

import Control.Comonad.Cofree (Cofree, head)
import Control.Monad.Except (runExceptT)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (runStateT)
import Data.Either (Either(..))
import Data.Functor.Mu (Mu)
import Data.Traversable (traverse)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class.Console (logShow)
import Language.Category.App (App)
import Language.Category.Forall (Forall)
import Language.Category.Hole (Hole)
import Language.Category.Var (class Fresh, Var)
import Language.Functor.Coproduct (type (:+:))
import Language.Functor.Parse (parser)
import Language.Functor.Reduction (infer, reduce)
import Language.Functor.Universe (Universe, flatten)
import Language.Monad.Context (class Context, Ctx, emptyCtx)
import Matryoshka (embed, project)
import Parsing (ParseError, runParserT)

foofa :: Effect Unit
foofa = do

  goo <- parseFoo "forall a . a b c"
  logShow goo

  foo <- parseFoo "forall a . a"
  logShow foo
  case foo of
    Left _ -> pure unit
    Right fo -> do
       (i /\ ctx) <- flip runStateT (emptyCtx :: Ctx Var (Universe Mu Foo)) $ runExceptT $ infero fo >>= traverse reduca 
       case i of
         Left (_ :: String) -> pure unit
         Right t -> do
            logShow $ flatten $ head t 
            (z /\ _) <- flip runStateT ctx $ reduca $ head t
            logShow $ flatten z
            

  pure unit


type Foo = (Hole :+: Forall :+: App :+: Var)

parseFoo :: forall m . MonadRec m => String -> m (Either ParseError (Mu Bar))
parseFoo s = runParserT s (embed <$> parser)


 
infero :: forall m.
          Monad m
       => Context Var (Universe Mu Foo) m 
       => Mu Bar -> m (Cofree Bar (Universe Mu Foo))
infero = infer

type Bar = Forall :+: App :+: Var

reduco :: forall m.
          Monad m
       => Fresh m
       => Cofree Foo (Universe Mu Foo) -> m (Cofree Foo (Universe Mu Foo))
reduco = reduce

reduca :: forall m.
          Monad m
       => Fresh m
       => Universe Mu Foo -> m (Universe Mu Foo)
reduca = map embed <<< reduco <<< project

