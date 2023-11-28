module Language.Term.LetRec where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Foldable (class Foldable)
import Data.List (List(..), elem)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (class Traversable, traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Basis (class Basis, basisY)
import Language.Lambda.Calculus (LambdaF, abs, app, free)
import Language.Lambda.Inference (class IsType)
import Matryoshka (class Corecursive, class Recursive)
import Type.Proxy (Proxy(..))


type LetRec f var cat = Map var (f (LambdaF var cat))

type LetSeq f var cat = List (var /\ f (LambdaF var cat))


recSeq :: forall t f var cat m.
          Ord var
       => MonadRec m
       => Foldable cat
       => Recursive (f (LambdaF var cat)) (LambdaF var cat)
       => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
       => Traversable cat
       => Functor cat
       => Basis t m f var cat
       => IsType (f (LambdaF var cat))
       => Eq (f (LambdaF var cat))
       => Proxy t -> LetRec f var cat -> m (LetSeq f var cat)
recSeq p x = tailRecM go (Nil /\ x)
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
          selfrec :: Set var
          selfrec = Map.keys $ Map.filterWithKey (\v s -> Set.singleton v == s) refersInBlock
          selfrec' :: LetRec f var cat 
          selfrec' = Map.filterKeys (flip elem selfrec) rec
          dependents :: LetRec f var cat
          dependents = Map.filterKeys (not <<< flip elem standalone) rec  
       in if Map.size dependents > 0
            then 
              if Set.size selfrec > 0
                then do
                  let sr :: LetSeq f var cat
                      sr = Map.toUnfoldable selfrec'
                  (zz :: LetSeq f var cat) <- traverse (\(v /\ e) -> Tuple v <$> singFix p v e) sr
                  let u = Map.filterKeys (not <<< flip elem (standalone `Set.union` selfrec)) rec  
                  pure $ Loop ((bou <> independents <> zz) /\ u) 
                else do 
                   
                  -- FIXME this is an infinite loop if there is any recursion
                  -- TODO pull back (as arguments) any references to bindings in the block 
                  -- and rewrite using the `fix` operator
                  pure $ Loop ((bou <> independents) /\ dependents)
            else pure $ Done (bou <> independents)


singFix :: forall f var cat t m.
          Recursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
       => Ord var
       => Traversable cat
       => Functor cat
       => Basis t m f var cat
       => Monad m
       => IsType (f (LambdaF var cat))
       => Eq (f (LambdaF var cat))
       => Proxy t
       -> var
       -> f (LambdaF var cat)
       -> m (f (LambdaF var cat))
singFix p v lam = do
  y <- basisY p
  pure $ app y (abs v lam)

