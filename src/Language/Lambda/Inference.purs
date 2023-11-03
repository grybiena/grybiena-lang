module Language.Lambda.Inference where

import Prelude

import Data.Functor.Mu (Mu(..))
import Language.Lambda.Calculus (LambdaF(..))


class ArrowType t where
  arrowType :: t

arrow :: forall p i c . ArrowType (c (Mu (LambdaF p i c)))
      => Mu (LambdaF p i c) -> Mu (LambdaF p i c) -> Mu (LambdaF p i c)
arrow a b = (flip app a (cat arrowType)) `app` b

cat :: forall p i c. c (Mu (LambdaF p i c)) -> Mu (LambdaF p i c)
cat c = In (Cat c)

app :: forall p i c . Mu (LambdaF p i c) -> Mu (LambdaF p i c) -> Mu (LambdaF p i c)
app a b = In (App a b)

class
  ( Monad m
  , ArrowType (t (Mu (LambdaF i i t)))
  ) <= InferPat p i t m where
  withFresh :: p -> (Mu (LambdaF i i t) -> m (Mu (LambdaF i i t))) -> m (Mu (LambdaF i i t))

class
  ( Monad m
  , ArrowType (t (Mu (LambdaF i i t)))
  ) <= InferVar v i t m where
  inferVar :: v -> m (Mu (LambdaF i i t))

class InferCat p v c i t m where
  inferCat :: c (Mu (LambdaF p v c)) -> m (Mu (LambdaF i i t)) 
  inferCatApp :: t (Mu (LambdaF i i t)) -> Mu (LambdaF p v c) -> m (Mu (LambdaF i i t))
  invalidApp :: forall a . Mu (LambdaF i i t) -> Mu (LambdaF p v c) -> m a
 

class (Eq i, Monad m) <= Unification i t m where
  fresh :: m (Mu (LambdaF i i t))
  applyCurrentSubstitution :: Mu (LambdaF i i t) -> m (Mu (LambdaF i i t)) 
  replaceVarWithFresh :: i -> Mu (LambdaF i i t) -> m (Mu (LambdaF i i t))
  substitute :: i -> Mu (LambdaF i i t) -> m Unit 
  unificationError :: Mu (LambdaF i i t) -> Mu (LambdaF i i t) -> m Unit
  skolemize :: i -> Mu (LambdaF i i t) -> m (Mu (LambdaF i i t))


unify :: forall i t m . Unification i t m => Mu (LambdaF i i t) -> Mu (LambdaF i i t) -> m Unit
 
unify (In t1) (In t2) = go t1 t2
  where
    go (Var v1) (Var v2) | v1 == v2 = pure unit
    go (Var v) t = substitute v (In t)
    go t (Var v) = substitute v (In t)
    go (Abs v1 i1) (Abs v2 i2) = join $ unify <$> skolemize v1 i1 <*> skolemize v2 i2
    go (Abs v1 i1) _ = join $ unify <$> skolemize v1 i1 <*> pure (In t2)
    go _ (Abs _ _) = unify (In t2) (In t1)
    go (App a1 b1) (App a2 b2) = unify a1 a2 *> unify b1 b2
    go _ _ = unificationError (In t1) (In t2)

check :: forall p v c i t m .
         InferPat p i t m
      => InferVar v i t m
      => InferCat p v c i t m
      => Unification i t m
      => Mu (LambdaF p v c) -> Mu (LambdaF i i t) -> m Unit
check v t = do
  t' <- infer v
  unify t t'

infer :: forall p v c i t m .
         InferPat p i t m
      => InferVar v i t m
      => InferCat p v c i t m
      => Unification i t m
      => Mu (LambdaF p v c) -> m (Mu (LambdaF i i t)) 
infer (In val) =
  case val of
    Abs v b -> do
      withFresh v $ \t -> do
        t' <- infer b
        pure $ arrow t t'
    App f a -> do
      In ft <- infer f
      checkApp ft a
    Var v -> inferVar v
    Cat c -> inferCat c
  where
    checkApp :: LambdaF i i t (Mu (LambdaF i i t)) -> (Mu (LambdaF p v c)) -> m (Mu (LambdaF i i t))
    checkApp (App (In (App arrowType' argTy)) retTy) arg = do
      unify arrowType' (cat arrowType)
      argTy' <- applyCurrentSubstitution argTy
      check arg argTy'
      pure retTy
    checkApp (Abs i t) arg = do
      In t' <- replaceVarWithFresh i t
      checkApp t' arg
    checkApp (Var i) arg = do
      argTy <- infer arg
      retTy <- fresh
      unify (In (Var i)) (arrow argTy retTy)
      pure retTy
    checkApp (Cat c) arg = inferCatApp c arg
    checkApp f arg = invalidApp (In f) arg

