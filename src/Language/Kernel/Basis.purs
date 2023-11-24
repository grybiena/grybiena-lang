module Language.Kernel.Basis where

import Prelude

import Language.Native.Unsafe (UnsafeNative(..))
import Unsafe.Coerce (unsafeCoerce)


basis ::
  { "S" :: UnsafeNative
  , "K" :: UnsafeNative
  , "I" :: UnsafeNative
  }
basis = 
  { "S": UnsafeNative
         { unsafeType: "forall a b c. (a -> b -> c) -> (a -> b) -> a -> c" 
         , nativeTerm:
             let exp :: forall a b c. (a -> b -> c) -> (a -> b) -> a -> c 
                 exp x y z = x z (y z)
              in unsafeCoerce exp
         } 
  , "K": UnsafeNative
         { unsafeType: "forall a b. a -> b -> a" 
         , nativeTerm:
             let exp :: forall a b. a -> b -> a
                 exp = const
              in unsafeCoerce exp 
         } 
  , "I": UnsafeNative
         { unsafeType: "forall a. a -> a" 
         , nativeTerm:
             let exp :: forall a. a -> a
                 exp = identity
              in unsafeCoerce exp

         } 
  }



