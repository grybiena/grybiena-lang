module Pretty.Printer where

import Control.Category (identity, (<<<))
import Data.Functor.Mu (Mu(..))
import Data.Show (show)
import Data.TacitString (TacitString)
import Language.Lambda.Calculus (class PrettyLambda, Lambda, LambdaF(..), prettyAbs, prettyApp, prettyCat, prettyVar)
import Prettier.Printer (DOC, text)
import Prettier.Printer as PP


class Pretty a where
  pretty :: a -> DOC 

instance Pretty DOC where
  pretty = identity
else
instance Pretty TacitString where
  pretty = text <<< show
instance PrettyLambda var cat => Pretty (Lambda var cat) where
  pretty (In l) =
    case l of
      Abs i a -> prettyAbs i a
      App f a -> prettyApp f a
      Var i -> prettyVar i
      Cat c -> prettyCat c

prettyPrint :: forall a . Pretty a => a -> String
prettyPrint a = PP.pretty 80 (pretty a)

