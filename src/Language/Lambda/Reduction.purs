module Language.Lambda.Reduction where

import Prelude

import Control.Comonad.Cofree (Cofree)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Eq (class Eq1)
import Data.Traversable (class Traversable)
import Effect.Class (class MonadEffect)
import Language.Lambda.Basis (class Basis)
import Language.Lambda.Calculus (class FreeVars, class Shadow, LambdaF)
import Language.Lambda.Elimination (class Composition, class Reduction, eliminate)
import Language.Lambda.Inference (class ArrowObject, class Inference, class IsTypeApp)
import Language.Lambda.Judgement (class Reasoning)
import Language.Lambda.Unification (class Context, class Fresh, class NotInScopeError, class Skolemize, class Substitute, class Unify)
import Language.Lambda.Unification.Error (class ThrowUnificationError)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive)
import Type.Proxy (Proxy)


elimReduce :: forall t f var cat m.
             Recursive (f (LambdaF var var cat)) (LambdaF var var cat) 
         => Corecursive (f (LambdaF var var cat)) (LambdaF var var cat) 
         => Composition f var cat m
         => Reduction f var cat m
         => Eq (f (LambdaF var var cat))
         => MonadRec m
         => MonadEffect m
         => Ord var
         => Traversable cat
         => Functor cat
         => Basis t m f var cat
         => IsTypeApp var var cat (f (LambdaF var var cat))
         => Fresh (f (LambdaF var var cat)) m
         => Ord var
         => NotInScopeError var m
         => Context var (f (LambdaF var var cat)) m
         => Shadow var
         => Fresh var m
         => Fresh Int m
         => Skolemize f var cat
         => Substitute var cat f m
         => Unify (cat (f (LambdaF var var cat))) (cat (f (LambdaF var var cat))) m
         => Unify var (f (LambdaF var var cat)) m
         => ThrowUnificationError (f (LambdaF var var cat)) m 
         => ArrowObject (cat (f (LambdaF var var cat))) 
         => Inference var var cat (f (LambdaF var var cat)) m 
         => FreeVars var var cat
         => Reasoning f var var cat m
         => Eq1 cat
         => Proxy t
         -> Cofree (LambdaF var var cat) (f (LambdaF var var cat))
         -> m (Cofree (LambdaF var var cat) (f (LambdaF var var cat)))
elimReduce p l = tailRecM go l
  where go x = do
          y <- eliminate p x
          if x == y 
            then pure $ Done y 
            else pure $ Loop y 
 

