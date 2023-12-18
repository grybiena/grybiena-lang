module Language.Functor.Type.Universe where

import Control.Alt (class Functor, (<$>))
import Control.Category ((<<<))
import Control.Comonad.Cofree (Cofree, head, tail)
import Data.Functor.Mu (Mu)
import Matryoshka (embed, project)

type Universe typ = Mu (Cofree typ)

ascend :: forall typ. Functor typ => Universe typ -> Universe typ
ascend = head <<< project

flatten :: forall typ. Functor typ => Universe typ -> Mu typ 
flatten = squash <<< project

squash :: forall typ. Functor typ => Cofree typ (Mu (Cofree typ)) -> Mu typ
squash g = embed (squash <$> tail g) 

