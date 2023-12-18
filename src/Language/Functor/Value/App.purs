module Language.Functor.Value.App where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Comonad.Env (EnvT(..), runEnvT)
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable)
import Data.Tuple (snd)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Application (class Application)
import Language.Category.Elimination (class Elimination)
import Language.Category.Inference (class Inference)
import Language.Category.Reduction (infer)
import Language.Functor.Coproduct (class Inject, type (:+:), Coproduct(..), inj, prj)
import Language.Functor.Type.App as Type
import Language.Functor.Type.Lit (Lit(..))
import Language.Functor.Type.Universe (Universe)
import Language.Functor.Value.Opaque (Opaque(..))
import Language.Lambda.Inference (class Arrow, unifyWithArrow)
import Language.Lambda.Unification (class Fresh, class Rewrite, class Unify, rewrite, unify)
import Matryoshka (class Corecursive, class Recursive, embed, project)


newtype App a = App (a /\ a)

instance Application App where
  app f g = App (f /\ g)
  unApp (App a) = a

instance
  ( Monad m
--  , Recursive (Universe t) tt
--  , Corecursive (Universe t) tt
  , Recursive (t (Universe u t)) t
  , Fresh (Universe u t) m
  , Rewrite (Universe u t) m
  , Arrow (Universe u t) 
  , Unify (Universe u t) (Universe u t) m
--  , Inject Var tt
--  , Inject (Abs App) tt
  , Inject App cat 
  , Inject Type.App t
  , Inject (Lit (Universe u t)) cat
  , Traversable t
  , Inference t t (Universe u t) m
  , Corecursive (u (Cofree t)) (Cofree t)
  ) => Inference App cat (Universe u t) m where
    inference (App (inferF /\ inferA)) = do 
      (f :: Cofree cat (Universe u t)) <- inferF
      a <- inferA
      case prj (tail a) of
        Just (Lit t) -> do
          z <- infer ((inj (Type.App (head f /\ t))) :: t (Universe u t))
          pure $ embed z :< tail f
        Nothing -> do

--      case Tuple <$> prj (project (head f)) <*> prj (tail a) of
--        Just ((Abs (v /\ b) :: Abs App var _) /\ (Lit (argLit :: t))) -> do
--          _ <- unify (embed (inj (Var v)) :: t) argLit
--          tyApp <- rewrite b
--          pure $ tyApp :< tail f
--        Nothing -> do
          arrArg /\ arrRet <- unifyWithArrow (head f)
          void $ unify arrArg (head a)
          arrRet' <- rewrite arrRet
          pure $ arrRet' :< (inj (App (f /\ a))) 
 
instance
  ( Monad m
  , Composition cat cat t m
  , Functor cat
  ) => Elimination App cat t m where
    elimination (App (a /\ b)) t =  composition (project a) (project b) t

class Composition obj cat t m where
  composition :: EnvT t obj (Cofree cat t) -> EnvT t obj (Cofree cat t) -> t -> m (Cofree cat t)

instance
  ( Composition a cat t m
  , Composition b cat t m
  , Applicative m
  , Inject App cat
  , Inject a cat
  , Inject b cat
  ) => Composition (a :+: b) cat t m where
    composition f g t =
      case runEnvT f /\ runEnvT g of
        (ta /\ Inl a) /\ (tb /\ Inl b) -> composition (EnvT (ta /\ a))  (EnvT (tb /\ b)) t
        (ta /\ Inr a) /\ (tb /\ Inr b) -> composition (EnvT (ta /\ a))  (EnvT (tb /\ b)) t
        (ta /\ Inl a) /\ (tb /\ Inr b) -> pure $ t :< inj (App ((ta :< inj a) /\ (tb :< inj b))) 
        (ta /\ Inr a) /\ (tb /\ Inl b) -> pure $ t :< inj (App ((ta :< inj a) /\ (tb :< inj b))) 
else
instance
  ( Applicative m
  , Inject Opaque cat
  ) => Composition Opaque cat t m where
    composition f g t = do
      let Opaque a = snd $ runEnvT f
          Opaque b = snd $ runEnvT g 
      pure $ t :< inj (Opaque { pretty: "(" <> a.pretty <> " " <> b.pretty <> ")"
                                    , term: a.term b.term
                                    })
else
instance
  ( Applicative m
  , Inject App cat
  , Inject obj cat
  ) => Composition obj cat t m where
    composition f g t =
      case runEnvT f /\ runEnvT g of
        (ta /\ a) /\ (tb /\b) -> pure $ t :< inj (App ((ta :< inj a) /\ (tb :< inj b))) 
 
