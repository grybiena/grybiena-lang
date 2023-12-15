module Language.Lambda.Judgement where

import Prelude

import Control.Comonad.Cofree (Cofree, head)
import Control.Monad.Writer (class MonadWriter, tell)
import Data.List (List, singleton)
import Language.Lambda.Calculus (LambdaF, flat)
import Matryoshka (class Corecursive, class Recursive)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty)

class Reasoning f abs var cat m where
  unifyTerms :: f (LambdaF abs var cat) -> f (LambdaF abs var cat) -> m Unit
  makeSubstitution :: var -> f (LambdaF abs var cat) -> m Unit
  assumeHasType :: var -> f (LambdaF abs var cat) -> m Unit
  inferred :: (Cofree (LambdaF abs var cat) (f (LambdaF var var cat))) -> m Unit


data Judgement f abs var cat = 
    UnifyTerms (f (LambdaF abs var cat)) (f (LambdaF abs var cat))
  | MakeSubstitution var (f (LambdaF abs var cat))
  | AssumeHasType var (f (LambdaF abs var cat))
  | Inferred (Cofree (LambdaF abs var cat) (f (LambdaF var var cat)))

 
instance
  ( MonadWriter (List (Judgement f abs var cat)) m
  ) => Reasoning f abs var cat m where
  unifyTerms a b = tell (singleton $ UnifyTerms a b)
  makeSubstitution v t = tell (singleton $ MakeSubstitution v t)
  assumeHasType v t = tell (singleton $ AssumeHasType v t)
  inferred t = tell (singleton $ Inferred t)

instance
  ( Pretty var
  , Pretty (f (LambdaF abs var cat))
  , Pretty (f (LambdaF var var cat))
  , Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
  , Corecursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
  , Functor cat
  ) => Pretty (Judgement f abs var cat) where
  pretty (UnifyTerms a b) = pretty a <+> text "=?=" <+> pretty b
  pretty (MakeSubstitution v t) = pretty v <+> text "==>>" <+> pretty t 
  pretty (AssumeHasType v t) = text "!" <+> pretty v <+> text "::" <+> pretty t 
  pretty (Inferred t) = text "$" <+> pretty (flat t :: (f (LambdaF abs var cat))) <+> text "::" <+> pretty (head t)

