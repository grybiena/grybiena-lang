module Language.Functor.Universe where

import Control.Alt (class Functor, (<$>))
import Control.Category ((<<<))
import Control.Comonad.Cofree (Cofree, head, tail)
import Matryoshka (class Corecursive, class Recursive, embed, project)

type Universe :: forall k. ((Type -> Type) -> k) -> (Type -> Type) -> k
type Universe u t = u (Cofree t)

ascend :: forall u t.
          Functor t
       => Recursive (u (Cofree t)) (Cofree t)
       => Universe u t -> Universe u t 
ascend = head <<< project

flatten :: forall u t.
           Functor t
        => Recursive (u (Cofree t)) (Cofree t)
        => Corecursive (u t) t
        => Universe u t -> u t 
flatten = squash <<< project

squash :: forall u t.
          Functor t
       => Corecursive (u t) t
       => Cofree t (u (Cofree t)) -> u t
squash g = embed (squash <$> tail g) 

