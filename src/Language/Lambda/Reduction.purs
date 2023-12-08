module Language.Lambda.Reduction where

import Prelude

import Control.Comonad.Cofree (Cofree)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Traversable (class Traversable)
import Effect.Class (class MonadEffect)
import Language.Lambda.Basis (class Basis)
import Language.Lambda.Calculus (class Shadow, LambdaF)
import Language.Lambda.Elimination (class Composition, class Reduction, eliminate)
import Language.Lambda.Inference (class ArrowObject, class Inference, class IsTypeApp, flat)
import Language.Lambda.Unification (class Context, class Fresh, class NotInScopeError, class Skolemize, class Substitute, class Unify)
import Language.Lambda.Unification.Error (class ThrowUnificationError)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive)
import Type.Proxy (Proxy)


elimReduce :: forall t f var cat m.
             Recursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Corecursive (f (LambdaF var cat)) (LambdaF var cat) 
         => Composition f var cat m
         => Reduction f var cat m
         => Eq (f (LambdaF var cat))
         => MonadRec m
         => MonadEffect m
         => Ord var
         => Traversable cat
         => Functor cat
         => Basis t m f var cat
         => IsTypeApp var cat (f (LambdaF var cat))
         => Fresh (f (LambdaF var cat)) m
         => Ord var
         => NotInScopeError var m
         => Context var (f (LambdaF var cat)) m
         => Shadow var
         => Fresh var m
         => Fresh Int m
         => Skolemize f var cat
         => Substitute var cat f m
         => Unify (cat (f (LambdaF var cat))) (cat (f (LambdaF var cat))) m
         => Unify var (f (LambdaF var cat)) m
         => ThrowUnificationError (f (LambdaF var cat)) m 
         => ArrowObject (cat (f (LambdaF var cat))) 
         => Inference var cat (f (LambdaF var cat)) m 
         => Proxy t
         -> Cofree (LambdaF var cat) (f (LambdaF var cat))
         -> m (Cofree (LambdaF var cat) (f (LambdaF var cat)))
elimReduce p l = tailRecM go l
  where go x = do
          y <- eliminate p x
          if flat y == flat x
            then pure $ Done y 
            else pure $ Loop y 
 

