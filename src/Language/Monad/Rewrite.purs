module Language.Monad.Rewrite where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable, traverse)
import Language.Category.Var (Var(..))
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Context, replace)
import Matryoshka (class Corecursive, class Recursive, embed, project)

class Rewrite a m where
  rewrite :: a -> m a

instance
  ( Inject Var t
  , Recursive (u (Cofree t)) (Cofree t) 
  , Corecursive (u (Cofree t)) (Cofree t) 
  , Monad m
  , Traversable t
  , Context Var (Universe u t) m
  ) => Rewrite (Universe u t) m where
  rewrite t = do
    let q :: t (Universe u t)
        q = embed <$> (tail $ project t)
    case prj q of
      Just (Var v) -> do
        (r :: Var Void -> Maybe (Universe u t)) <- replace
        case r (Var v) of
          Nothing -> do
            h <- rewrite (head (project t))
            pure (embed (h :< inj (Var v)))
          Just so -> pure so
      Nothing -> do
         h <- rewrite (head (project t))
         r <- map project <$> traverse rewrite q
         pure $ embed (h :< r)

