module Language.Category.Reduction where

import Prelude

import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env (EnvT, runEnvT)
import Data.Traversable (class Traversable)
import Data.Tuple (uncurry)
import Matryoshka (class Recursive, cata, cataM, embed, project)
import Language.Category.Elimination (class Elimination, elimination)
import Language.Category.Inference (class Inference, inference)

class (Functor obj, Functor cat) <= Reduction obj f g cat m where
  reduction :: obj f -> m (cat g)

instance 
  ( Inference obj cat typ m
  ) => Reduction obj (m (Cofree cat typ)) typ (Cofree cat) m where
  reduction = inference


infer :: forall exp cat typ m.
          Reduction cat (m (Cofree cat typ)) typ (Cofree cat) m
       => Recursive exp cat
       => exp -> m (Cofree cat typ) 
infer = cata reduction 

instance 
  ( Functor obj 
  , Functor cat
  , Monad m
  , Elimination obj cat typ m
  ) => Reduction (EnvT typ obj) (Cofree cat typ) (Cofree cat typ) (EnvT typ cat) m where
    reduction e = project <$> uncurry (flip elimination) (runEnvT e)

reduce :: forall obj cat typ m.
          Elimination obj cat typ m
       => Monad m
       => Traversable obj 
       => Functor cat
       => Cofree obj typ -> m (Cofree cat typ) 
reduce = cataM (map embed <<< reduction) 


