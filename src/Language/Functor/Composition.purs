module Language.Functor.Composition where

import Prelude

import Control.Comonad.Cofree (Cofree, (:<))
import Control.Comonad.Env (EnvT(..), runEnvT)
import Data.Tuple (snd)
import Data.Tuple.Nested ((/\))
import Language.Category.Opaque (Opaque(..))
import Language.Functor.Application (class Application, app)
import Language.Functor.Coproduct (class Inject, type (:+:), Coproduct(..), inj)


class Composition app obj cat t m | cat -> app where
  composition :: EnvT t obj (Cofree cat t) -> EnvT t obj (Cofree cat t) -> t -> m (Cofree cat t)

instance
  ( Composition app a cat t m
  , Composition app b cat t m
  , Applicative m
  , Inject app cat
  , Inject a cat
  , Inject b cat
  , Application app
  ) => Composition app (a :+: b) cat t m where
    composition f g t =
      case runEnvT f /\ runEnvT g of
        (ta /\ Inl a) /\ (tb /\ Inl b) -> composition (EnvT (ta /\ a))  (EnvT (tb /\ b)) t
        (ta /\ Inr a) /\ (tb /\ Inr b) -> composition (EnvT (ta /\ a))  (EnvT (tb /\ b)) t
        (ta /\ Inl a) /\ (tb /\ Inr b) -> pure $ t :< inj (app (ta :< inj a) (tb :< inj b) :: app (Cofree cat t)) 
        (ta /\ Inr a) /\ (tb /\ Inl b) -> pure $ t :< inj (app (ta :< inj a) (tb :< inj b) :: app (Cofree cat t)) 
else
instance
  ( Applicative m
  , Inject Opaque cat
  ) => Composition app Opaque cat t m where
    composition f g t = do
      let Opaque a = snd $ runEnvT f
          Opaque b = snd $ runEnvT g 
      pure $ t :< inj (Opaque { pretty: "(" <> a.pretty <> " " <> b.pretty <> ")"
                                    , term: a.term b.term
                                    })
else
instance
  ( Applicative m
  , Inject app cat
  , Inject obj cat
  , Application app
  ) => Composition app obj cat t m where
    composition f g t =
      case runEnvT f /\ runEnvT g of
        (ta /\ a) /\ (tb /\b) -> pure $ t :< inj (app (ta :< inj a) (tb :< inj b) :: app (Cofree cat t)) 
 
