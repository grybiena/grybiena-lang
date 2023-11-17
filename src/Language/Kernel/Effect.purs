module Language.Kernel.Effect where

import Prelude

import Data.Homogeneous.Record (homogeneous)
import Effect (Effect)
import Language.Term (TT(..), Var, Term)
import Language.Lambda.Calculus (abs, absMany, app, cat, var)
import Language.Lambda.Inference ((:->:))
import Language.Lambda.Unification (class Fresh, fresh)
import Language.Module (Module)
import Language.Value.Native (Native(..))
import Unsafe.Coerce (unsafeCoerce)


pureEffect :: forall m. Monad m => Fresh Var m => m (Native Term)
pureEffect = do
  a <- fresh
  pure $ Purescript
    { nativeType: abs a $ var a :->: (app (cat TypeEffect) (var a))
    , nativeTerm:
        let prim :: forall a. a -> Effect a
            prim = pure
         in unsafeCoerce prim
    }
 
bindEffect :: forall m. Monad m => Fresh Var m => m (Native Term)
bindEffect = do
  a <- fresh
  b <- fresh
  pure $ Purescript
    { nativeType: absMany [a,b]
                $ (app (cat TypeEffect) (var a))
             :->: (var a :->: (app (cat TypeEffect) (var b)))
             :->: (app (cat TypeEffect) (var b))
    , nativeTerm:
        let prim :: forall a b. Effect a -> (a -> Effect b) -> Effect b
            prim = (>>=)
         in unsafeCoerce prim
    }

type EffectTermListing =
  ( pureEffect :: Void                     
  , bindEffect :: Void
  )
 
effectNatives :: forall m.
     Monad m
  => Fresh Var m
  => Module
      EffectTermListing
      (m (Native Term))
effectNatives = homogeneous
  { "pureEffect": pureEffect
  , "bindEffect": bindEffect
  }



