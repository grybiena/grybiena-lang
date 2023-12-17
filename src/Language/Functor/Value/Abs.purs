module Language.Functor.Value.Abs where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Application (class Application, app, unApp)
import Language.Category.Elimination (class Elimination)
import Language.Category.Inference (class Inference, inference)
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Value.Basis (Basis(..))
import Language.Functor.Value.Var (Var(..))
import Language.Lambda.Inference (class Arrow, (:->:))
import Language.Lambda.Unification (class Context, class Fresh, class Rewrite, assume, fresh, rewrite)


newtype Abs :: forall k. k -> Type -> Type -> Type
newtype Abs app var a = Abs (var /\ a)

instance
  ( Monad m
  , Context var typ m
  , Fresh typ m
  , Rewrite typ m
  , Arrow typ
  , Inject (Abs app var) cat 
  ) => Inference (Abs app var) cat typ m where
    inference (Abs (binding /\ inferBody)) = do 
      tyBind <- fresh
      assume binding tyBind
      tyBody <- inferBody
      argTy <- rewrite tyBind 
      pure $ (argTy :->: (head tyBody)) :< inj (Abs (binding /\ tyBody) :: Abs app var _)

class FreeIn var cat typ where
  freeIn :: var -> Cofree cat typ -> Boolean

instance
  ( Monad m
  , Functor cat
  , Inject (Var var) cat
  , Inject Basis cat
  , Inject app cat
  , Inject (Abs app var) cat
  , Application app
  , Inference Basis cat typ m
  , Inference app cat typ m
  , FreeIn var cat typ
  , Eq var
  ) => Elimination (Abs app var) cat typ m where
    elimination (Abs (a /\ x)) t = do
      case prj (tail x) of
        Just (Var v) | v == a -> pure $ t :< inj I 
        Just (Var _) -> do
          k <- inference K  
          pure $ t :< inj (app k x :: app (Cofree cat typ))
        Nothing ->
          case prj (tail x) of
            Just (Abs ((_ :: var) /\ f) :: Abs app var _) | a `freeIn` f ->
              pure $ t :< inj (Abs (a /\ x) :: Abs app var _)
            Just _ -> do
              k <- inference K
              pure $ t :< inj (app k x :: app (Cofree cat typ))
            Nothing ->
              case unApp <$> (prj (tail x) :: Maybe (app (Cofree cat typ))) of
                Just (e1 /\ e2) -> do
                  case a `freeIn` e1 /\ a `freeIn` e2 of
                    true /\ true -> do
                      s <- inference (app (inference S) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ t :< inj (app s e2 :: app (Cofree cat typ))
                    true /\ false -> do
                      c <- inference (app (inference C) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ t :< inj (app c e2 :: app (Cofree cat typ))
                    false /\ true -> do
                      b <- inference (app (inference B) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ t :< inj (app b e2 :: app (Cofree cat typ))                    
                    _ -> do 
                      if a `freeIn` x
                        then pure $ t :< inj (Abs (a /\ x) :: Abs app var _)
                        else do
                          k <- inference K
                          pure $ t :< inj (app k x :: app (Cofree cat typ))
                Nothing -> pure $ t :< inj (Abs (a /\ x) :: Abs app var _)
 

