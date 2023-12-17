module Language.Functor.Value.App where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Comonad.Env (EnvT(..), runEnvT)
import Data.Functor.Mu (Mu(..))
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
import Matryoshka (class Recursive, project)


newtype App a = App (a /\ a)

instance Application App where
  app f g = App (f /\ g)
  unApp (App a) = a

instance
  ( Monad m
--  , Recursive (Universe typ) tt
--  , Corecursive (Universe typ) tt
  , Recursive (typ (Universe typ)) typ
  , Fresh (Universe typ) m
  , Rewrite (Universe typ) m
  , Arrow (Universe typ) 
  , Unify (Universe typ) (Universe typ) m
--  , Inject Var tt
--  , Inject (Abs App) tt
  , Inject App cat 
  , Inject Type.App typ
  , Inject (Lit (Universe typ)) cat
  , Elimination typ typ (Mu (Cofree typ)) m
  , Traversable typ
  , Inference typ typ (Universe typ) m
  ) => Inference App cat (Universe typ) m where
    inference (App (inferF /\ inferA)) = do 
      (f :: Cofree cat (Universe typ)) <- inferF
      a <- inferA
      case prj (tail a) of
        Just (Lit t) -> do
          z <- infer ((inj (Type.App (head f /\ t))) :: typ (Universe typ))
          pure $ In z :< tail f
        Nothing -> do

--      case Tuple <$> prj (project (head f)) <*> prj (tail a) of
--        Just ((Abs (v /\ b) :: Abs App var _) /\ (Lit (argLit :: typ))) -> do
--          _ <- unify (embed (inj (Var v)) :: typ) argLit
--          tyApp <- rewrite b
--          pure $ tyApp :< tail f
--        Nothing -> do
          arrArg /\ arrRet <- unifyWithArrow (head f)
          void $ unify arrArg (head a)
          arrRet' <- rewrite arrRet
          pure $ arrRet' :< (inj (App (f /\ a))) 
 
instance
  ( Monad m
  , Composition cat cat typ m
  , Functor cat
  ) => Elimination App cat typ m where
    elimination (App (a /\ b)) t =  composition (project a) (project b) t

class Composition obj cat typ m where
  composition :: EnvT typ obj (Cofree cat typ) -> EnvT typ obj (Cofree cat typ) -> typ -> m (Cofree cat typ)

instance
  ( Composition a cat typ m
  , Composition b cat typ m
  , Applicative m
  , Inject App cat
  , Inject a cat
  , Inject b cat
  ) => Composition (a :+: b) cat typ m where
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
  ) => Composition Opaque cat typ m where
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
  ) => Composition obj cat typ m where
    composition f g t =
      case runEnvT f /\ runEnvT g of
        (ta /\ a) /\ (tb /\b) -> pure $ t :< inj (App ((ta :< inj a) /\ (tb :< inj b))) 
 
