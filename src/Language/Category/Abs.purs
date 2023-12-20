module Language.Category.Abs where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Basis (Basis(..))
import Language.Category.Var (Var(..))
import Language.Functor.Application (class Application, app, unApp)
import Language.Functor.Arrow (class Arrow, (:=>:))
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference, inference)
import Language.Functor.Unification (class Unification)
import Language.Monad.Context (class Context, assume)
import Language.Monad.Fresh (class Fresh, fresh)
import Language.Monad.Rewrite (class Rewrite, rewrite)


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



instance
  ( Monad m
  ) => Unification (Abs app) (Abs app) i m where
    unification _ _ = pure Nil 



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
        Just v | v == a -> pure $ Just $ t :< inj I 
        Just _ -> do
          k <- inference K  
          pure $ Just $ t :< inj (app k x :: app (Cofree cat typ))
        Nothing ->
          case prj (tail x) of
            Just (Abs (_ /\ f) :: Abs app _) | a `freeIn` f ->
              pure Nothing 
            Just _ -> do
              k <- inference K
              pure $ Just $ t :< inj (app k x :: app (Cofree cat typ))
            Nothing ->
              case unApp <$> (prj (tail x) :: Maybe (app (Cofree cat typ))) of
                Just (e1 /\ e2) -> do
                  case a `freeIn` e1 /\ a `freeIn` e2 of
                    true /\ true -> do
                      s <- inference (app (inference S) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ Just $ t :< inj (app s e2 :: app (Cofree cat typ))
                    true /\ false -> do
                      c <- inference (app (inference C) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ Just $ t :< inj (app c e2 :: app (Cofree cat typ))
                    false /\ true -> do
                      b <- inference (app (inference B) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ Just $ t :< inj (app b e2 :: app (Cofree cat typ))                    
                    _ -> do 
                      if a `freeIn` x
                        then pure Nothing 
                        else do
                          k <- inference K
                          pure $ Just $ t :< inj (app k x :: app (Cofree cat typ))
                Nothing -> pure Nothing 
 

