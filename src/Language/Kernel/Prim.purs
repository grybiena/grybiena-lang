module Language.Kernel.Prim where


import Data.Array ((:))
import Data.Maybe (Maybe(..))
import Language.Native.Unsafe (UnsafeNative(..))
import Unsafe.Coerce (unsafeCoerce)

primNatives ::
  { "ifElse" :: UnsafeNative "forall a. Boolean -> a -> a -> a"
  , "Nothing" :: UnsafeNative "forall a. Maybe a"
  , "Just" :: UnsafeNative "forall a. a -> Maybe a"
  , "nullArray" :: UnsafeNative "forall a. Array a" 
  , "consArray" :: UnsafeNative "forall a. a -> Array a -> Array a"
  }
primNatives = 
  { "ifElse": UnsafeNative
       let prim :: forall a. Boolean -> a -> a -> a
           prim x a b = if x then a else b
        in unsafeCoerce prim 
  , "Nothing": UnsafeNative
       let prim :: forall a. Maybe a 
           prim = Nothing 
        in unsafeCoerce prim 
  , "Just": UnsafeNative
       let prim :: forall a. a -> Maybe a 
           prim = Just 
        in unsafeCoerce prim 
  , "nullArray": UnsafeNative
       let prim :: forall a. Array a
           prim = []
        in unsafeCoerce prim
  , "consArray": UnsafeNative
       let prim :: forall a. a -> Array a -> Array a
           prim a r = a:r
        in unsafeCoerce prim
  }



