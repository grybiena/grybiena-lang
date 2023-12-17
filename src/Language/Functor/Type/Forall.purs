module Language.Functor.Type.Forall where

import Prelude

import Control.Comonad.Cofree (Cofree, (:<))
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Context (class Context, assume)
import Language.Category.Elimination (class Elimination)
import Language.Category.Inference (class Inference)
import Language.Category.Reduction (infer, reduce)
import Language.Functor.Coproduct (class Inject, type (:+:), inj)
import Language.Functor.Ident.Hole (Hole, hole)
import Language.Functor.Ident.Var (class Fresh, Var(..))
import Language.Functor.Parse (class Parse, parse)
import Language.Functor.Type.Universe (Universe)
import Language.Parser (class LanguageParser, reserved, reservedOp)
import Matryoshka (class Corecursive, embed)


newtype Forall a = Forall (Var a /\ a)

instance Functor Forall where
  map f (Forall (v /\ a)) = Forall ((f <$> v) /\ f a)


instance Foldable Forall where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

instance Traversable Forall where
  traverse f (Forall (v /\ a)) = Forall <$> (Tuple <$> traverse f v <*> f a) 
  sequence = traverse identity

instance
  ( Monad m
  , Context Var (Universe typ) m
  , Inject Forall cat 
  , Inject Hole typ
  ) => Inference Forall cat (Universe typ) m where
    inference (Forall (Var v /\ inferBody)) = do 
      assume (Var v) (hole :: Universe typ) 
      inferBody

instance 
  ( Monad m
  , Inject Forall cat
  ) => Elimination Forall cat typ m where
    elimination v t = pure (t :< inj v)

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

type Foo = (Forall :+: Var :+: Hole)


parso :: forall m.
         LanguageParser m
      => Monad m
      => m (Mu (Foo))
parso = parse
 
infero :: forall m.
          Monad m
       => Context Var (Universe Foo) m 
       => Mu Foo -> m (Cofree Foo (Universe Foo))
infero = infer

reduco :: forall m. Monad m => Fresh m => Cofree Foo (Universe Foo) -> m (Cofree Foo (Universe Foo))
reduco = reduce

