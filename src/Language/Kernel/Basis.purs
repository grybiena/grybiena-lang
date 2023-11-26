module Language.Kernel.Basis where

import Prelude

import Control.Lazy (fix)
import Language.Native.Unsafe (UnsafeNative(..))
import Unsafe.Coerce (unsafeCoerce)


basis ::
  { "S" :: UnsafeNative "forall a b c. (a -> b -> c) -> (a -> b) -> a -> c" 
  , "K" :: UnsafeNative "forall a b. a -> b -> a" 
  , "I" :: UnsafeNative "forall a. a -> a" 
  , "C" :: UnsafeNative "forall a b c. (b -> a -> c) -> a -> b -> c"
  , "B" :: UnsafeNative "forall a b c. (b -> c) -> (a -> b) -> a -> c"
  , "Y" :: UnsafeNative "forall a b. ((a -> b) -> (a -> b)) -> (a -> b)"
  }
basis = 
  { "S": UnsafeNative
           let exp :: forall a b c. (a -> b -> c) -> (a -> b) -> a -> c 
               exp x y z = x z (y z)
            in unsafeCoerce exp
  , "K": UnsafeNative
           let exp :: forall a b. a -> b -> a
               exp = const
            in unsafeCoerce exp 
  , "I": UnsafeNative
           let exp :: forall a. a -> a
               exp = identity
            in unsafeCoerce exp
  , "C": UnsafeNative
           let exp :: forall a b c. (b -> a -> c) -> a -> b -> c
               exp x y z = (x z) y
            in unsafeCoerce exp 
  , "B": UnsafeNative
           let exp :: forall a b c. (b -> c) -> (a -> b) -> a -> c
               exp x y z = x (y z)
            in unsafeCoerce exp
  , "Y": UnsafeNative
           let exp :: forall a b. ((a -> b) -> (a -> b)) -> (a -> b)
               exp = fix
            in unsafeCoerce exp
  }

