module Language.Lambda.Calculus where

import Prelude

import Control.Alt (class Functor, map, (<$>))
import Control.Category ((<<<))
import Data.Eq (class Eq, class Eq1, eq1, (==))
import Data.Foldable (class Foldable, foldr)
import Data.Functor.Mu (Mu)
import Data.Generic.Rep (class Generic)
import Data.Show (class Show)
import Data.Show.Generic (genericShow)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Prettier.Printer (DOC, text)

-- | Un-Fixed LambdaF 
data LambdaF pat var cat a =
    Abs pat a
  | App a a
  | Var var
  | Cat (cat a)

type Lambda pat var cat = Mu (LambdaF pat var cat)

derive instance Generic (LambdaF pat var cat a) _

instance
  ( Eq pat
  , Eq var
  , Eq1 cat
  ) => Eq1 (LambdaF pat var cat) where
  eq1 (Abs i _) (Abs j _) = i == j
  eq1 (App _ _) (App _ _) = true
  eq1 (Var i) (Var j) = i == j
  eq1 (Cat a) (Cat b) = eq1 a b
  eq1 _ _ = false

instance
  ( Show pat
  , Show var
  , Show (cat a)
  , Show a
  ) => Show (LambdaF pat var cat a) where
  show = genericShow

instance Functor cat => Functor (LambdaF pat var cat) where
  map f (Abs i a) = Abs i (f a)
  map f (App a b) = App (f a) (f b)
  map _ (Var i) = Var i
  map f (Cat c) = Cat (f <$> c)

class PrettyVar i where
  prettyVar :: i -> DOC

instance PrettyVar String where
  prettyVar = text

class (PrettyVar pat, PrettyVar var) <= PrettyLambda pat var cat where
  prettyAbs :: pat -> Lambda pat var cat -> DOC
  prettyApp :: Lambda pat var cat -> Lambda pat var cat -> DOC
  prettyCat :: cat (Lambda pat var cat) -> DOC



embedVar :: forall f lam pat var cat .
            Functor f
         => Corecursive lam (LambdaF pat var cat)
         => f var -> f lam
embedVar = map (embed <<< Var)


embedApp :: forall f lam pat var cat .
            Functor f
         => Corecursive lam (LambdaF pat var cat)
         => lam -> f lam -> f lam
embedApp a = map (embed <<< App a)

embedAbs :: forall f t lam pat var cat .
            Functor f
         => Apply f
         => Functor t
         => Foldable t
         => Corecursive lam (LambdaF pat var cat)
         => f (t pat) -> f lam -> f lam
embedAbs pats body =
  let bindPats :: f (t (lam -> lam))
      bindPats = map (\b -> embed <<< Abs b) <$> pats
  in flip (foldr ($)) <$> bindPats <*> body

 



