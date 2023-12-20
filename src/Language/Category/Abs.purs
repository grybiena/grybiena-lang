module Language.Category.Abs where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Basis (Basis(..))
import Language.Category.Hole (Hole)
import Language.Functor.Application (class Application, app, unApp)
import Language.Functor.Arrow (class Arrow, (:=>:))
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Elimination (class Elimination)
import Language.Functor.Inference (class Inference, inference)
import Language.Functor.Unification (class Unification)
import Language.Functor.Universe (Universe)
import Language.Monad.Context (class Context, class Rewrite, class Variable, assume, rewrite, variable)
import Language.Monad.Fresh (class Fresh, freshHole)
import Matryoshka (class Corecursive, class Recursive)
import Type.Proxy (Proxy(..))


newtype Abs :: forall k. (Type -> Type) -> k -> Type -> Type
newtype Abs var app a = Abs (var a /\ a)

instance
  ( Monad m
  , Context var (Universe u t) m
  , Inject var t
  , Traversable t
  , Recursive (u (Cofree t)) (Cofree t)
  , Corecursive (u (Cofree t)) (Cofree t)
  , Fresh (var (Cofree t (Universe u t))) m 
  , Rewrite var (Universe u t) m
  , Arrow (Universe u t) 
  , Inject (Abs var app) cat 
  , Inject Hole t
  , Variable var
  ) => Inference var (Abs var app) cat (Universe u t) m where
    inference p (Abs (v /\ inferBody)) = do 
      tyBind <- freshHole p
      assume (void v) tyBind
      tyBody <- inferBody
      argTy <- rewrite (Proxy :: Proxy var) tyBind
      pure $ (argTy :=>: (head tyBody)) :< inj (Abs (variable v /\ tyBody) :: Abs var app _)



instance
  ( Monad m
  ) => Unification (Abs var app) (Abs var app) t i m where
    unification _ _ = pure Nil 



class FreeIn var cat typ where
  freeIn :: var -> Cofree cat typ -> Boolean

instance
  ( Monad m
  , Functor cat
  , Inject var cat
  , Inject Basis cat
  , Inject app cat
  , Inject (Abs var app) cat
  , Application app
  , Inference var Basis cat typ m
  , Inference var app cat typ m
  , FreeIn (var (Cofree cat typ)) cat typ
  , Eq (var (Cofree cat typ))
  ) => Elimination (Abs var app) cat typ m where
    elimination (Abs (a /\ x)) t = do
      case prj (tail x) of
        Just v | v == a -> pure $ Just $ t :< inj I 
        Just _ -> do
          k <- inference (Proxy :: Proxy var) K  
          pure $ Just $ t :< inj (app k x :: app (Cofree cat typ))
        Nothing ->
          case prj (tail x) of
            Just (Abs (_ /\ f) :: Abs var app _) | a `freeIn` f ->
              pure Nothing 
            Just _ -> do
              k <- inference (Proxy :: Proxy var) K
              pure $ Just $ t :< inj (app k x :: app (Cofree cat typ))
            Nothing ->
              case unApp <$> (prj (tail x) :: Maybe (app (Cofree cat typ))) of
                Just (e1 /\ e2) -> do
                  case a `freeIn` e1 /\ a `freeIn` e2 of
                    true /\ true -> do
                      s <- inference (Proxy :: Proxy var) (app (inference (Proxy :: Proxy var) S) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ Just $ t :< inj (app s e2 :: app (Cofree cat typ))
                    true /\ false -> do
                      c <- inference (Proxy :: Proxy var) (app (inference (Proxy :: Proxy var) C) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ Just $ t :< inj (app c e2 :: app (Cofree cat typ))
                    false /\ true -> do
                      b <- inference (Proxy :: Proxy var) (app (inference (Proxy :: Proxy var) B) (pure e1) :: app (m (Cofree cat typ)))
                      pure $ Just $ t :< inj (app b e2 :: app (Cofree cat typ))                    
                    _ -> do 
                      if a `freeIn` x
                        then pure Nothing 
                        else do
                          k <- inference (Proxy :: Proxy var) K
                          pure $ Just $ t :< inj (app k x :: app (Cofree cat typ))
                Nothing -> pure Nothing 
 

