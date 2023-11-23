module Language.Term.LetRec where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Foldable (class Foldable)
import Data.List (List(..), elem)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (LambdaF, free)
import Matryoshka (class Recursive)


type LetRec f var cat = Map var (f (LambdaF var cat))

type LetSeq f var cat = List (var /\ f (LambdaF var cat))


recSeq :: forall f var cat.
          Ord var
       => Foldable cat
       => Recursive (f (LambdaF var cat)) (LambdaF var cat)
       => LetRec f var cat -> LetSeq f var cat
recSeq x = tailRec go (Nil /\ x)
  where
    go (bou /\ rec) = 
      let boundInBlock :: Set var
          boundInBlock = Map.keys rec
          refersInBlock :: Map var (Set var)
          refersInBlock = (Set.filter (flip elem boundInBlock) <<< free) <$> rec
          standalone :: Set var
          standalone = Map.keys $ Map.filter (eq 0 <<< Set.size) refersInBlock
          independents :: LetSeq f var cat
          independents = Map.toUnfoldable $ Map.filterKeys (flip elem standalone) rec 
          dependents :: LetRec f var cat
          dependents = Map.filterKeys (not <<< flip elem standalone) rec  
       in if Map.size dependents > 0
            then 
              -- FIXME this is an infinite loop if there is any recursion
              -- TODO pull back (as arguments) any references to bindings in the block 
              -- and rewrite using the `fix` operator
              Loop ((bou <> independents) /\ dependents)
            else Done (bou <> independents)


