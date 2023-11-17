module Language.Kernel.Effect where

import Prelude

import Data.Homogeneous.Record (homogeneous)
import Effect (Effect)
import Language.Lambda.Calculus (abs, absMany, app, var)
import Language.Lambda.Inference ((:->:))
import Language.Lambda.Unification (class Fresh, fresh)
import Language.Module (Module)
import Language.Term (Term, Var)
import Language.Term.Reify (reify)
import Language.Value.Native (Native(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)



pureEffect :: forall m. Monad m => Fresh Var m => m (Native Term)
pureEffect = do
  let typeEffect :: Term
      typeEffect = reify (Proxy :: Proxy Effect)
  a <- fresh
  pure $ Purescript
    { nativeType: abs a $ var a :->: (app typeEffect (var a))
    , nativePretty: "pureEffect"
    , nativeTerm:
        let prim :: forall a. a -> Effect a
            prim = pure
         in unsafeCoerce prim
    }
 
bindEffect :: forall m. Monad m => Fresh Var m => m (Native Term)
bindEffect = do
  --TODO use the parser
  --t <- parseType "Effect a -> (a -> Effect b) -> Effect b"
  --nativeType <- renameFresh t

  let typeEffect :: Term
      typeEffect = reify (Proxy :: Proxy Effect)

  a <- fresh
  b <- fresh
  pure $ Purescript
    { nativeType: absMany [a,b]
                $ (app typeEffect (var a))
             :->: (var a :->: (app typeEffect (var b)))
             :->: (app typeEffect (var b))
    , nativePretty: "bindEffect"
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



