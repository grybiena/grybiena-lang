module Language.Kernel.Effect where

import Prelude

import Effect (Effect)
import Language.Native.Meta (MetaNative(..))
import Unsafe.Coerce (unsafeCoerce)



pureEffect :: MetaNative
pureEffect =
  MetaNative
    { metaType: "forall a. a -> Effect a"
    , nativeTerm:
        let prim :: forall a. a -> Effect a
            prim = pure
         in unsafeCoerce prim
    }

 
bindEffect :: MetaNative
bindEffect = 
  MetaNative
    { metaType: "forall a b. Effect a -> (a -> Effect b) -> Effect b"
    , nativeTerm:
        let prim :: forall a b. Effect a -> (a -> Effect b) -> Effect b
            prim = (>>=)
         in unsafeCoerce prim
    }


effectNatives ::
  { bindEffect :: MetaNative
  , pureEffect :: MetaNative
  }
effectNatives = 
  { "pureEffect": pureEffect
  , "bindEffect": bindEffect
  }



