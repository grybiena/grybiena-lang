module Language.Term.LetRec where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRec, tailRecM)
import Data.Foldable (class Foldable, fold, foldr, null)
import Data.List (List(..), concat, elem, head, partition, (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (LambdaF, free)
import Matryoshka (class Recursive)


type LetRec f var cat = Map var (f (LambdaF var cat))

type LetSeq f var cat = List (var /\ f (LambdaF var cat))


recSeq :: forall f var cat m.
          Ord var
       => MonadRec m
       => Foldable cat
       => Recursive (f (LambdaF var cat)) (LambdaF var cat)
       => LetRec f var cat -> m (LetSeq f var cat)
recSeq x = tailRecM go (Nil /\ x)
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
          dependents :: LetRec f var cat
          dependents = Map.filterKeys (not <<< flip elem standalone) rec  
       in if Map.size dependents > 0
            then 
               
              -- FIXME this is an infinite loop if there is any recursion
              -- TODO pull back (as arguments) any references to bindings in the block 
              -- and rewrite using the `fix` operator
              pure $ Loop ((bou <> independents) /\ dependents)
            else pure $ Done (bou <> independents)

-- 1. pull out non-recursive
-- 2. fix purely self recursive
-- 3. fix mutually recursive via graph traversal

type Vertex f var cat =
  { boundAs :: var
  , term :: f (LambdaF var cat)
  , refersTo :: Set var
  }

newtype Block f var cat = Block (Map var (f (LambdaF var cat)))

newtype Graph var = Graph (Map var (Set var))

newtype Edge var = Edge (var /\ var)
derive newtype instance Eq var => Eq (Edge var)
derive newtype instance Show var => Show (Edge var)

newtype Edges var = Edges (List (Edge var))
derive newtype instance Eq var => Eq (Edges var)
derive newtype instance Show var => Show (Edges var)
derive newtype instance Semigroup (Edges var)
derive newtype instance Monoid (Edges var)


newtype Points var = Points (Set var)
derive newtype instance Eq var => Eq (Points var)
derive newtype instance Show var => Show (Points var)
derive newtype instance Ord var => Semigroup (Points var)
derive newtype instance Ord var => Monoid (Points var)
derive newtype instance Foldable Points

bound :: forall f var cat. Block f var cat -> Set var 
bound (Block b) = Map.keys b

graph :: forall f var cat.
         Ord var
      => Foldable cat
      => Recursive (f (LambdaF var cat)) (LambdaF var cat)
      => Block f var cat -> Graph var 
graph block@(Block b) = Graph ((Set.filter (flip elem (bound block)) <<< free) <$> b)

edges :: forall var. Graph var -> Edges var
edges (Graph g) =
  let squash :: List (var /\ List var)
      squash = map Set.toUnfoldable <$> Map.toUnfoldable g
      pair :: (var /\ List var) -> List (Edge var)
      pair (v /\ rs) = Edge <<< Tuple v <$> rs
   in Edges (join (pair <$> squash))

class Pointed f where
  points :: forall a. Ord a => f a -> Points a 

instance Pointed Edge where
  points (Edge (a /\ b)) = Points $ Set.insert a (Set.singleton b)

instance Pointed Edges where
  points (Edges e) = fold (points <$> e)

instance Pointed Graph where
  points = points <<< edges


class Intersects a b where
  intersects :: a -> b -> Boolean


instance Ord var => Intersects (Points var) (Points var) where
  intersects (Points a) (Points b) = not $ null $ Set.intersection a b
else
instance (Pointed a, Pointed b, Ord var) => Intersects (a var) (b var) where
  intersects a b = intersects (points a) (points b) 


 
  
class Components f where
  components :: forall var. Ord var => f var -> List (f var)



instance Components Edges where
  components e = tailRec findComponents (Nil /\ e) 
    where
      findComponents :: (List (Edges _) /\ Edges _) -> Step (List (Edges _) /\ Edges _) (List (Edges _))
      findComponents (d /\ t) =
        case saturateFirst t of
          (f /\ Edges Nil) -> Done (f:d)
          (f /\ g) -> Loop ((f:d) /\ g)
  
        where
          saturateFirst :: Edges _ -> (Edges _/\ Edges _)
          saturateFirst = tailRec saturate <<< groupFirst 
            where
              saturate :: (Edges _/\ Edges _) -> Step (Edges _ /\ Edges _) (Edges _ /\ Edges _)
              saturate x@(_ /\ Edges Nil) = Done x
              saturate (f /\ Edges r) =
                let { yes, no } = partition (intersects f) r
                  in if r == no
                       then Done ((f <> Edges yes) /\ Edges no)
                       else Loop ((f <> Edges yes) /\ Edges no)
           
              groupFirst :: Edges _ -> (Edges _ /\ Edges _)
              groupFirst (Edges Nil) = Edges Nil /\ Edges Nil 
              groupFirst (Edges (a:r)) =
                let { yes, no } = partition (intersects a) r
                  in Edges (a:yes) /\ Edges no
            
