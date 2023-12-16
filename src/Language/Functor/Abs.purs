module Language.Functor.Abs where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Category.Application (class Application, app, unApp)
import Language.Category.Elimination (class Elimination)
import Language.Category.Inference (class Inference, inference)
import Language.Functor.Basis (Basis(..))
import Language.Functor.Coproduct (class Inject, inj, prj)
import Language.Functor.Var (Var(..))
import Language.Lambda.Inference (class Arrow, (:->:))
import Language.Lambda.Unification (class Context, class Fresh, class Rewrite, assume, fresh, rewrite)
import Unsafe.Coerce (unsafeCoerce)


newtype Abs var a = Abs (var /\ a)

instance
  ( Monad m
  , Context var typ m
  , Fresh typ m
  , Rewrite typ m
  , Arrow typ
  , Inject (Abs var) cat 
  ) => Inference (Abs var) cat typ m where
    inference (Abs (binding /\ inferBody)) = do 
      tyBind <- fresh
      assume binding tyBind
      assume binding tyBind 
      tyBody <- inferBody
      tyBind' <- rewrite tyBind 
      pure $ (tyBind' :->: (head tyBody)) :< inj (Abs (binding /\ tyBody))

class FreeIn var cat typ where
  freeIn :: var -> Cofree cat typ -> Boolean

instance
  ( Monad m
  , Functor cat
  , Inject (Var var) cat
  , Inject Basis cat
  , Inject app cat
  , Inject (Abs var) cat
  , Application app
  , Inference Basis cat typ m
  , Inference app cat typ m
  , FreeIn var cat typ
  , Eq var
  ) => Elimination (Abs var) cat typ m where
    elimination (Abs (a /\ x)) t = do
      case prj (tail x) of
        Just (Var v) | v == a -> pure $ t :< inj I 
        Just (Var _) -> do
          k <- inference K  
          pure $ t :< inj (app k x :: app (Cofree cat typ))
        Nothing ->
          case prj (tail x) of
            Just (Abs ((_ :: var) /\ f)) | a `freeIn` f -> pure $ t :< inj (Abs (a /\ x))
            Just _ -> do
              k <- inference K
              pure $ t :< inj (app k x :: app (Cofree cat typ))
            Nothing ->
              case unApp <$> (prj (tail x) :: Maybe (app (Cofree cat typ))) of
                Just (e1 /\ e2) | a `freeIn` e1 && a `freeIn` e2 -> do
                  s <- inference S
                  s' <- inference (app (pure s) (pure e1) :: app (m (Cofree cat typ)))
                  pure $ t :< inj (app s' e2 :: app (Cofree cat typ))
                Just (e1 /\ e2) -> unsafeCoerce unit
                Nothing -> unsafeCoerce unit


