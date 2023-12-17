module Language.Functor.Value.Abs where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Application (class Application, app, unApp)
import Language.Category.Arrow (class Arrow, (:=>:))
import Language.Category.Context (class Context, assume)
import Language.Category.Elimination (class Elimination)
import Language.Category.Fresh (class Fresh, fresh)
import Language.Category.Inference (class Inference, inference)
import Language.Category.Rewrite (class Rewrite, rewrite)
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Ident.Var (Var(..))
import Language.Functor.Value.Basis (Basis(..))



newtype Abs :: forall k. k -> Type -> Type
newtype Abs app a = Abs (Var a /\ a)

instance
  ( Monad m
  , Context Var typ m
  , Fresh typ m
  , Rewrite typ m
  , Arrow typ
  , Inject (Abs app) cat 
  ) => Inference (Abs app) cat typ m where
    inference (Abs (Var v /\ inferBody)) = do 
      tyBind <- fresh
      assume (Var v) tyBind
      tyBody <- inferBody
      argTy <- rewrite tyBind 
      pure $ (argTy :=>: (head tyBody)) :< inj (Abs (Var v /\ tyBody) :: Abs app _)

class FreeIn var cat typ where
  freeIn :: var -> Cofree cat typ -> Boolean

instance
  ( Monad m
  , Functor cat
  , Inject Var cat
  , Inject Basis cat
  , Inject app cat
  , Inject (Abs app) cat
  , Application app
  , Inference Basis cat typ m
  , Inference app cat typ m
  , FreeIn (Var (Cofree cat typ)) cat typ
  , Eq var
  ) => Elimination (Abs app) cat typ m where
    elimination (Abs (a /\ x)) t = do
      case prj (tail x) of
        Just v | v == a -> pure $ t :< inj I 
        Just _ -> do
          k <- inference K  
          pure $ t :< inj (app k x :: app (Cofree cat typ))
        Nothing ->
          case prj (tail x) of
            Just (Abs (_ /\ f) :: Abs app _) | a `freeIn` f ->
              pure $ t :< inj (Abs (a /\ x) :: Abs app _)
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
                        then pure $ t :< inj (Abs (a /\ x) :: Abs app _)
                        else do
                          k <- inference K
                          pure $ t :< inj (app k x :: app (Cofree cat typ))
                Nothing -> pure $ t :< inj (Abs (a /\ x) :: Abs app _)
 

