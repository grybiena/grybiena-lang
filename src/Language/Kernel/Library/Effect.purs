module Language.Kernel.Library.Effect where

import Prelude

import Data.Homogeneous.Record (homogeneous)
import Language.Grybu (TT(..), Var, Term)
import Language.Kernel.Library (KernelLibrary)
import Language.Lambda.Calculus (abs, absMany, app, cat, var)
import Language.Lambda.Inference ((:->:))
import Language.Lambda.Unification (class Fresh, fresh)
import Language.Value.Native (Native(..))
import Unsafe.Coerce (unsafeCoerce)


pureEffect :: forall n m. Monad m => Fresh Var m => Applicative n => m (Native (Term n))
pureEffect = do
  a <- fresh
  pure $ Purescript
    { nativeType: abs a $ var a :->: (app (cat TypeEffect) (var a))
    , nativeTerm:
        let prim :: forall a. a -> m a
            prim = pure
         in unsafeCoerce prim
    }
 
bindEffect :: forall n m. Monad m => Fresh Var m => Bind n => m (Native (Term n))
bindEffect = do
  a <- fresh
  b <- fresh
  pure $ Purescript
    { nativeType: absMany [a,b]
                $ (app (cat TypeEffect) (var a))
             :->: (var a :->: (app (cat TypeEffect) (var b)))
             :->: (app (cat TypeEffect) (var b))
    , nativeTerm:
        let prim :: forall a b. m a -> (a -> m b) -> m b
            prim = (>>=)
         in unsafeCoerce prim
    }

type EffectTermListing =
  ( pureEffect :: Void                     
  , bindEffect :: Void
  )
 
effectNatives :: forall m n.
     Monad m
  => Fresh Var m
  => Monad n
  => KernelLibrary
      EffectTermListing
      (m (Native (Term n)))
effectNatives = homogeneous
  { "pureEffect": pureEffect
  , "bindEffect": bindEffect
  }


