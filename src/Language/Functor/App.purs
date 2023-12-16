module Language.Functor.App where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Comonad.Env (EnvT(..), runEnvT)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), snd)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Application (class Application)
import Language.Category.Elimination (class Elimination)
import Language.Category.Inference (class Inference)
import Language.Functor.Abs (Abs(..))
import Language.Functor.Coproduct (class Inject, type (:+:), Coproduct(..), inj, prj)
import Language.Functor.Opaque (Opaque(..))
import Language.Functor.Var (Var(..))
import Language.Lambda.Inference (class Arrow, unifyWithArrow)
import Language.Lambda.Unification (class Fresh, class Rewrite, class Unify, rewrite, unify)
import Matryoshka (class Corecursive, class Recursive, embed, project)

newtype Lit :: forall k. Type -> k -> Type
newtype Lit lit a = Lit lit 


newtype App a = App (a /\ a)

instance Application App where
  app f g = App (f /\ g)
  unApp (App a) = a

instance
  ( Monad m
  , Recursive typ tt
  , Corecursive typ tt
  , Fresh typ m
  , Rewrite typ m
  , Arrow typ 
  , Unify typ typ m
  , Inject (Var var) tt
  , Inject (Abs var) tt
  , Inject App cat 
  , Inject (Lit typ) cat
  ) => Inference App cat typ m where
    inference (App (inferF /\ inferA)) = do 
      f <- inferF
      a <- inferA
      case Tuple <$> prj (project (head f)) <*> prj (tail a) of
        Just (Abs ((v :: var) /\ b) /\ Lit (argLit :: typ)) -> do
          _ <- unify (embed (inj (Var v)) :: typ) argLit
          tyApp <- rewrite b
          pure $ tyApp :< tail f
        Nothing -> do
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
 
