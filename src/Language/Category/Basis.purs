module Language.Category.Basis where

import Prelude

import Control.Comonad.Cofree ((:<))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Language.Category.Opaque (Opaque(..))
import Language.Functor.Coproduct (class Inject, inj)
import Unsafe.Coerce (unsafeCoerce)
import Language.Functor.Elimination (class Elimination)

data Basis :: forall k. k -> Type
data Basis a = S | K | I | B | C

derive instance Generic (Basis a) _

instance Show (Basis a) where
  show = genericShow

instance Functor Basis where
  map _ b = unsafeCoerce b

nativePretty :: forall q v. Basis q -> Opaque v
nativePretty basis =
  let s :: forall a b c. (a -> b -> c) -> (a -> b) -> a -> c
      s x y z = x z (y z)
      k :: forall a b. a -> b -> a
      k = const
      i :: forall a. a -> a
      i = identity
      c :: forall a b c. (b -> a -> c) -> a -> b -> c
      c x y z = (x z) y
      b :: forall a b c. (b -> c) -> (a -> b) -> a -> c
      b x y z = x (y z)
  in case basis of
    S -> Opaque { pretty: (show basis), term: (unsafeCoerce s) } 
    K -> Opaque { pretty: (show basis), term: (unsafeCoerce k) } 
    I -> Opaque { pretty: (show basis), term: (unsafeCoerce i) }  
    C -> Opaque { pretty: (show basis), term: (unsafeCoerce c) } 
    B -> Opaque { pretty: (show basis), term: (unsafeCoerce b) } 

instance
  ( Monad m
  , Inject Opaque cat 
  ) => Elimination Basis cat typ m where
    elimination b t = pure $ t :< inj (nativePretty b)


