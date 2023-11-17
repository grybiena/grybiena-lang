module Language.Type.Reify where

import Effect (Effect)
import Language.Term (TT(..), Term)
import Language.Lambda.Calculus (app, cat)
import Language.Value.Native (Native(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

reifyNative :: forall t . Reify t => t -> Native Term
reifyNative term = Purescript
  { nativeType: reify (Proxy :: Proxy t)
  , nativeTerm: unsafeCoerce term
  }


class Reify :: forall k. k -> Constraint
class Reify s where
  reify :: Proxy s -> Term

instance Reify (->) where
  reify _ = cat Arrow

instance Reify Effect where
  reify _ = cat TypeEffect

instance Reify Int where
  reify _ = cat TypeInt

instance Reify Number where
  reify _ = cat TypeNumber

instance (Reify a, Reify b) => Reify (a b) where
  reify _ = app (reify (Proxy :: Proxy a)) (reify (Proxy :: Proxy b))

