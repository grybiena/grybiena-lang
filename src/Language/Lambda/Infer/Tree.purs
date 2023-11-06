module Language.Lambda.Infer.Tree where

import Prelude

import Control.Comonad.Cofree ((:<))
import Control.Monad.State (StateT, modify_, runStateT)
import Data.List (List(..))
import Data.Maybe (Maybe(..), maybe)
import Data.Tree (Tree)
import Data.Tree.Zipper (Loc, fromTree, insertAfter, insertChild, modifyValue, toTree, up)
import Data.Tuple.Nested (type (/\))

class Reckon :: forall k. k -> (k -> Type) -> Constraint
class Reckon j m where
  reckon :: m j -> m j

type Reckoner j m = StateT (Loc (Maybe j)) m

runReckoner :: forall j m a. Monad m => Reckoner j m a -> m (a /\ Tree (Maybe j))
runReckoner f = map toTree <$> runStateT f (fromTree (Nothing :< Nil)) 

instance Monad m => Reckon j (Reckoner j m) where
  reckon infer = do
    modify_ (insertChild (Nothing :< Nil) <<< insertAfter (Nothing :< Nil))
    j <- infer
    modify_ (\st -> maybe st (modifyValue (const $ Just j)) (up st))
    pure j

