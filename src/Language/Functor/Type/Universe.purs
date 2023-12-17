module Language.Functor.Type.Universe where

import Control.Alt (class Functor)
import Control.Category ((<<<))
import Control.Comonad.Cofree (Cofree, head)
import Data.Functor.Mu (Mu)
import Matryoshka (project)

type Universe typ = (Cofree typ (Mu (Cofree typ)))

ascend :: forall typ. Functor typ => Universe typ -> Universe typ
ascend = project <<< head
