module Language.Functor.Reduction where

import Prelude

import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env (EnvT, mapEnvT, runEnvT)
import Control.Lazy (fix)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Maybe (maybe)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (uncurry)
import Debug (traceM)
import Language.Functor.Coproduct (class Inject, inj)
import Language.Functor.Elimination (class Eliminated, class Elimination, eliminated, elimination, eliminations)
import Language.Functor.Inference (class Inference, inference)
import Language.Functor.Universe (Universe)
import Matryoshka (class Corecursive, class Recursive, cata, cataM, embed, project)
import Type.Proxy (Proxy(..))

class (Functor obj, Functor cat) <= Reduction obj f g cat m where
  reduction :: obj f -> m (cat g)

instance 
  ( Inference var obj cat typ m
  , Functor obj
  , Functor cat
  ) => Reduction obj (m (Cofree cat typ)) typ (Cofree cat) m where
  reduction = inference (Proxy :: Proxy var)


infer :: forall var exp cat typ m.
          Inference var cat cat typ m
       => Recursive exp cat
       => Proxy var -> exp -> m (Cofree cat typ) 
infer p = cata (inference p) 

instance 
  ( Monad m
  , Functor cat
  , Eliminated m
  , Elimination obj cat typ m
  , Inject obj cat
  ) => Reduction (EnvT typ obj) (Cofree cat typ) (Cofree cat typ) (EnvT typ cat) m where
    reduction e = uncurry (flip elimination) (runEnvT e)
            >>= maybe (pure $ mapEnvT inj e) (\x -> eliminated *> pure (project x)) 

reduceU :: forall u t m.
          Elimination t t (Universe u t) m
       => Eliminated m
       => Monad m
       => Recursive (u (Cofree t)) (Cofree t) 
       => Corecursive (u (Cofree t)) (Cofree t) 
       => Traversable t
       => (Cofree t (Universe u t) -> m (Cofree t (Universe u t)))
       -> Cofree t (Universe u t) -> m (Cofree t (Universe u t)) 
reduceU r x = do
  i <- eliminations
  y <- reduce x
  j <- eliminations
  if j > i
    then traverse (map embed <<< r <<< project) y
    else pure y

reduceFixU :: forall u t m.
          Elimination t t (Universe u t) m
       => Eliminated m
       => MonadRec m
       => Recursive (u (Cofree t)) (Cofree t) 
       => Corecursive (u (Cofree t)) (Cofree t) 
       => Traversable t
       => Cofree t (Universe u t) -> m (Cofree t (Universe u t)) 
reduceFixU = tailRecM go
  where
    go x = do
       i <- eliminations
       y <- (fix reduceU) x 
       j <- eliminations
       traceM $ "eliminations: " <> show (j - i)
       pure if j > i then Loop y else Done y



reduce :: forall obj cat typ m.
          Elimination obj cat typ m
       => Eliminated m
       => Monad m
       => Traversable obj 
       => Functor cat
       => Inject obj cat
       => Cofree obj typ -> m (Cofree cat typ) 
reduce = cataM (map embed <<< reduction)

reduceFix :: forall cat typ m.
          Elimination cat cat typ m
       => Eliminated m
       => MonadRec m
       => Traversable cat 
       => Functor cat
       => Cofree cat typ -> m (Cofree cat typ) 
reduceFix = tailRecM go
  where
    go x = do
       i <- eliminations
       y <- cataM (map embed <<< reduction) x 
       j <- eliminations
       traceM $ "eliminations: " <> show (j - i)
       pure if j > i then Loop y else Done y





