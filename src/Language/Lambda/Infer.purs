module Language.Lambda.Infer where

import Prelude

import Control.Monad.Writer (class MonadTell, tell)
import Data.Foldable (class Foldable)
import Data.Traversable (class Traversable, traverse)
import Language.Lambda.Calculus (LambdaF(..))
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Coalgebra (CoalgebraM)
import Matryoshka.Unfold (anaM)

class InferAbs :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class InferAbs pat exp juj m where
  inferAbs :: pat -> exp -> m (juj exp)


class AppRule :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class AppRule exp typ juj m | exp -> typ where
  appRule :: Typing exp typ -> Typing exp typ -> m (juj exp)
 
class InferVar :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class InferVar var exp juj m where
  inferVar :: var -> m (juj exp)

class InferCat :: (Type -> Type) -> Type -> (Type -> Type) -> (Type -> Type) -> Constraint
class InferCat cat exp juj m where
  inferCat :: cat exp -> m (juj exp)

infer :: forall typ juj m exp pat var cat.
          Corecursive typ juj
       => Monad m
       => Traversable juj
       => Recursive exp (LambdaF pat var cat)
       => InferAbs pat exp juj m
       => AppRule exp typ juj m
       => InferVar var exp juj m
       => InferCat cat exp juj m
       => MonadTell (juj exp) m
       => exp -> m (Typing exp typ)
infer exp = Typing exp <$> anaM go exp 
  where
    ju j = tell j *> pure j
    go :: CoalgebraM m juj exp
    go e = ju =<< case project e of
      Abs b a -> inferAbs b a
      App f a -> join $ appRule <$> infer f <*> infer a
      Var v -> inferVar v
      Cat c -> inferCat c


data Typing exp typ = Typing exp typ
 

data Judgement exp typ a =
    HasType exp typ
  | JudgeApp a a typ


instance Functor (Judgement exp typ) where
  map _ (HasType e i) = HasType e i
  map f (JudgeApp a b t) = JudgeApp (f a) (f b) t

instance Foldable (Judgement exp typ) where
  foldr _ b (HasType _ _) = b
  foldr f b (JudgeApp x y _) = f y (f x b) 
  foldl _ b (HasType _ _) = b
  foldl f b (JudgeApp x y _) = f (f b y) x
  foldMap _ (HasType _ _) = mempty
  foldMap f (JudgeApp x y _) = f x <> f y

instance Traversable (Judgement exp typ) where
  traverse _ (HasType e t) = pure $ HasType e t
  traverse f (JudgeApp a b t) = (\ta tb -> JudgeApp ta tb t) <$> f a <*> f b
  sequence = traverse identity


---- -- this is an Orphan instance but we can extract the type from the judgement like this
----instance Corecursive typ (Judgement ex typ) where
----  embed (HasType _ t) = t
----  embed (JudgeApp _ _ t) = t 
