module Language.Type.Reify where

import Language.Grybu (TT(..), Term)
import Language.Lambda.Calculus (app, cat)
import Language.Value.Native (Native(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

reifyNative :: forall m t . Reify t m => t -> Native (Term m)
reifyNative term = Purescript
  { nativeType: reify (Proxy :: Proxy t)
  , nativeTerm: unsafeCoerce term
  }

class Reify :: forall k. k -> (Type -> Type) -> Constraint
class Reify s m where
  reify :: Proxy s -> Term m

instance Reify (->) m where
  reify _ = cat Arrow

instance Reify Int m where
  reify _ = cat TypeInt

instance Reify Number m where
  reify _ = cat TypeNumber

instance (Reify a m, Reify b m) => Reify (a b) m where
  reify _ = app (reify (Proxy :: Proxy a)) (reify (Proxy :: Proxy b))

