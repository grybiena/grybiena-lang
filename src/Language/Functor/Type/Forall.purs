module Language.Functor.Type.Forall where

import Prelude

import Control.Comonad.Cofree (Cofree)
import Data.Functor.Mu (Mu)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Context (class Context, assume)
import Language.Category.Fresh (class Fresh, fresh)
import Language.Category.Inference (class Inference)
import Language.Category.Reduction (infer)
import Language.Functor.Coproduct (class Inject, type (:+:))
import Language.Functor.Ident.Var (Var(..))
import Language.Functor.Parse (class Parse, parse)
import Language.Functor.Type.Universe (Universe)
import Language.Parser (class LanguageParser, reserved, reservedOp)
import Matryoshka (class Corecursive, embed)


newtype Forall a = Forall (Var a /\ a)

instance Functor Forall where
  map f (Forall (v /\ a)) = Forall ((f <$> v) /\ f a)

instance
  ( Monad m
  , Fresh typ m
  , Context Var typ m
  , Inject Forall cat 
  ) => Inference Forall cat typ m where
    inference (Forall (Var v /\ inferBody)) = do 
      (tyBind :: typ) <- fresh
      assume (Var v) tyBind
      inferBody


instance
  ( LanguageParser m
  , Monad m
  , Corecursive (f cat) cat
  , Parse Var cat f m 
  , Parse cat cat f m
  ) => Parse Forall cat f m where
  parse = do
     reserved "forall"
     (v :: Var (f cat)) <- parse
     reservedOp "."
     (c :: cat (f cat)) <- parse 
     pure (Forall (v /\ embed c))

type Foo = (Forall :+: Var)

infero :: forall m.
          Monad m
       => Fresh (Universe Foo) m
       => Context Var (Universe Foo) m 
       => Mu Foo -> m (Cofree Foo (Universe Foo)) 
infero = infer

parso :: forall m.
         LanguageParser m
      => Monad m
      => m (Mu (Foo))
parso = parse
 
