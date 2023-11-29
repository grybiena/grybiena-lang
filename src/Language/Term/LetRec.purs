module Language.Term.LetRec where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (class Foldable)
import Data.Graph.LetRec (LetRec(..))
import Data.List (List, reverse)
import Data.Map as Map
import Data.Topos.Pointed.Projection (SCC(..), projection)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested (type (/\))
import Language.Lambda.Calculus (LambdaF)
import Language.Lambda.Inference (class IsType)
import Matryoshka (class Corecursive, class Recursive)

type LetSeq f var cat = List (var /\ f (LambdaF var cat))


recSeq :: forall f var cat.
          Ord var
       => Foldable cat
       => Recursive (f (LambdaF var cat)) (LambdaF var cat)
       => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
       => Traversable cat
       => Functor cat
       => IsType (f (LambdaF var cat))
       => Eq (f (LambdaF var cat))
       => LetRec f var cat ->  Either (LetRec f var cat) (LetSeq f var cat)
recSeq lr =
      let SCC (scc :: List (LetRec f var cat)) = projection lr
          failOnSCC :: LetRec f var cat -> Either (LetRec f var cat) (var /\ (f (LambdaF var cat)))
          failOnSCC (LetRec s) = case Map.toUnfoldable s of
                  [z] -> Right z
                  _ -> Left $ LetRec s
       in reverse <$> traverse failOnSCC scc

