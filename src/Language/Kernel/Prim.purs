module Language.Kernel.Prim where


import Language.Native.Unsafe (UnsafeNative(..))
import Unsafe.Coerce (unsafeCoerce)



ifElse ::
  UnsafeNative "forall a. Boolean -> a -> a -> a"
ifElse =
  UnsafeNative
    let prim :: forall a. Boolean -> a -> a -> a
        prim x a b = if x then a else b
     in unsafeCoerce prim
    


primNatives ::
  { ifElse :: UnsafeNative "forall a. Boolean -> a -> a -> a"
  }
primNatives = 
  { "ifElse": ifElse
  }



