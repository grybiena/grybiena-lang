module Test.Functor.Type where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail)
import Control.Lazy (fix)
import Control.Monad.Except (runExceptT)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (evalStateT, runStateT)
import Data.Either (Either(..))
import Data.Functor.Mu (Mu)
import Data.Traversable (traverse)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class.Console (log, logShow)
import Language.Category.Context (class Context, Ctx, emptyCtx)
import Language.Category.Reduction (infer, reduce)
import Language.Functor.Coproduct (type (:+:))
import Language.Functor.Ident.Hole (Hole)
import Language.Functor.Ident.Var (class Fresh, Var)
import Language.Functor.Parse (parse)
import Language.Functor.Type.Forall (Forall)
import Language.Functor.Type.Universe (Universe, flatten)
import Matryoshka (embed, project)
import Parsing (ParseError, runParserT)

foofa :: Effect Unit
foofa = do
--  foo <- parseFoo "a"
--  logShow foo

  foo <- parseFoo "forall a . a"
  logShow foo
  case foo of
    Left _ -> pure unit
    Right fo -> do
       (i /\ ctx) <- flip runStateT (emptyCtx :: Ctx Var (Universe Foo)) $ runExceptT $ infero fo >>= traverse reduca 
       case i of
         Left (_ :: String) -> pure unit
         Right t -> do
            logShow $ flatten $ head t 
            (z /\ _) <- flip runStateT ctx $ reduca $ head t
            logShow $ flatten z
            

  pure unit


type Foo = (Hole :+: Forall :+: Var)

parseFoo :: forall m . MonadRec m => String -> m (Either ParseError (Mu Bar))
parseFoo s = runParserT s (embed <$> fix parse)


 
infero :: forall m.
          Monad m
       => Context Var (Universe Foo) m 
       => Mu Bar -> m (Cofree Bar (Universe Foo))
infero = infer

type Bar = Forall :+: Var

reduco :: forall m.
          Monad m
       => Fresh m
       => Cofree Foo (Universe Foo) -> m (Cofree Foo (Universe Foo))
reduco = reduce

reduca :: forall m.
          Monad m
       => Fresh m
       => Universe Foo -> m (Universe Foo)
reduca = map embed <<< reduco <<< project

