module Language.Kernel.Effect where

import Prelude

import Effect (Effect)
import Language.Native.Unsafe (UnsafeNative(..))
import Unsafe.Coerce (unsafeCoerce)



pureEffect :: UnsafeNative
pureEffect =
  UnsafeNative
    { unsafeType: "forall a. a -> Effect a"
    , nativeTerm:
        let exp :: forall a. a -> Effect a
            exp = pure
         in unsafeCoerce exp
    }

 
bindEffect :: UnsafeNative
bindEffect = 
  UnsafeNative
    { unsafeType: "forall a b. Effect a -> (a -> Effect b) -> Effect b"
    , nativeTerm:
        let exp :: forall a b. Effect a -> (a -> Effect b) -> Effect b
            exp = (>>=)
         in unsafeCoerce exp
    }


effectNatives ::
  { bindEffect :: UnsafeNative
  , pureEffect :: UnsafeNative
  }
effectNatives = 
  { "pureEffect": pureEffect
  , "bindEffect": bindEffect
  }



