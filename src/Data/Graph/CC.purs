module Data.Graph.CC (cc) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Graph.Edge (Edge)
import Data.List (List(..), (:))
import Data.List as List
import Data.Topos.Intersects (intersects)
import Data.Tuple.Nested (type (/\), (/\))

type Graph v = List (Edge v)

cc :: forall v. Ord v => Graph v -> List (Graph v)
cc e = tailRec findComponents (Nil /\ e) 
    where
      findComponents :: (List (Graph v) /\ Graph v) -> Step (List (Graph v) /\ Graph v) (List (Graph v))
      findComponents (d /\ t) =
        case saturateFirst t of
          (f /\ Nil) -> Done (f:d)
          (f /\ g) -> Loop ((f:d) /\ g)
  
        where
          saturateFirst :: Graph v -> (Graph v/\ Graph v)
          saturateFirst = tailRec saturate <<< groupFirst 
            where
              saturate :: (Graph v/\ Graph v) -> Step (Graph v /\ Graph v) (Graph v /\ Graph v)
              saturate x@(_ /\ Nil) = Done x
              saturate (f /\ r) =
                let { yes, no } = List.partition (intersects f) r
                  in if r == no
                       then Done ((f <> yes) /\ no)
                       else Loop ((f <> yes) /\ no)
           
              groupFirst :: Graph v -> (Graph v /\ Graph v)
              groupFirst Nil = Nil /\ Nil 
              groupFirst (a:r) =
                let { yes, no } = List.partition (intersects a) r
                  in (a:yes) /\ no
 

