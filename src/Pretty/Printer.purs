module Pretty.Printer where

import Data.Functor.Mu (Mu(..))
import Language.Lambda.Calculus (class PrettyLambda, Lambda, LambdaF(..), prettyAbs, prettyApp, prettyCat, prettyVar)
import Prettier.Printer (DOC)
import Prettier.Printer as PP


class Pretty a where
  pretty :: a -> DOC 

instance PrettyLambda pat var cat => Pretty (Lambda pat var cat) where
  pretty (In l) =
    case l of
      Abs i a -> prettyAbs i a
      App f a -> prettyApp f a
      Var i -> prettyVar i
      Cat c -> prettyCat c

prettyPrint :: forall a . Pretty a => a -> String
prettyPrint a = PP.pretty 80 (pretty a)

