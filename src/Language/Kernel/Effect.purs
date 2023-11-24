module Language.Kernel.Effect where

import Prelude

import Effect (Effect)
import Language.Native.Unsafe (UnsafeNative(..))
import Unsafe.Coerce (unsafeCoerce)



pureEffect ::
  UnsafeNative "forall a. a -> Effect a"
pureEffect =
  UnsafeNative
    let prim :: forall a. a -> Effect a
        prim = pure
     in unsafeCoerce prim
    

 
bindEffect ::
  UnsafeNative "forall a b. Effect a -> (a -> Effect b) -> Effect b"
bindEffect = 
  UnsafeNative
    let prim :: forall a b. Effect a -> (a -> Effect b) -> Effect b
        prim = (>>=)
     in unsafeCoerce prim



effectNatives ::
  { bindEffect :: UnsafeNative "forall a b. Effect a -> (a -> Effect b) -> Effect b"
  , pureEffect :: UnsafeNative "forall a. a -> Effect a"
  }
effectNatives = 
  { "pureEffect": pureEffect
  , "bindEffect": bindEffect
  }



