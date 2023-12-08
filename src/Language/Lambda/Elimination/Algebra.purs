module Language.Lambda.Elimination.Algebra where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.Traversable (class Traversable, traverse)

-- Annotated with rules described here https://en.wikipedia.org/wiki/Combinatory_logic#Combinators_B,_C
data EliminationAlgebra var cat typ t =
    VarRule var typ     -- 1. T[x] ⇒ x 
  | AppRule typ t t     -- 2. T[(E₁ E₂)] ⇒ (T[E₁] T[E₂])
  | BasisK t            -- 3. T[λx.E] ⇒ (K T[E]) (if x is not free in E)
  | BasisI              -- 4. T[λx.x] ⇒ I
  | AbsRule typ var t   -- 5. T[λx.λy.E] ⇒ T[λx.T[λy.E]] (if x is free in E)
  | BasisS t t          -- 6. T[λx.(E₁ E₂)] ⇒ (S T[λx.E₁] T[λx.E₂]) (if x is free in both E₁ and E₂)
  | BasisC t t          -- 7. T[λx.(E₁ E₂)] ⇒ (C T[λx.E₁] T[E₂]) (if x is free in E₁ but not E₂)
  | BasisB t t          -- 8. T[λx.(E₁ E₂)] ⇒ (B T[E₁] T[λx.E₂]) (if x is free in E₂ but not E₁)
  | EtaReduce t         -- eta reduction. T[λx.a x] ⇒ T[a]
  | CatRule typ (cat t) -- cat reduction (by cat traversal)

instance Functor cat => Functor (EliminationAlgebra var cat typ) where
  map _ (VarRule var typ) = VarRule var typ
  map f (AppRule typ a b) = AppRule typ (f a) (f b)
  map f (BasisK a) = BasisK (f a)
  map _ BasisI = BasisI
  map f (AbsRule typ x a) = AbsRule typ x (f a)
  map f (BasisS a b) = BasisS (f a) (f b)
  map f (BasisC a b) = BasisC (f a) (f b)
  map f (BasisB a b) = BasisB (f a) (f b)
  map f (EtaReduce a) = EtaReduce (f a)
  map f (CatRule typ c) = CatRule typ (f <$> c)


 
instance Foldable cat => Foldable (EliminationAlgebra var cat typ) where
  foldr _ b (VarRule _ _) = b
  foldr f b (AppRule _ x y) = f x (f y b) 
  foldr f b (BasisK x) = f x b
  foldr _ b BasisI = b
  foldr f b (AbsRule _ _ x) = f x b
  foldr f b (BasisS x y) = f x (f y b) 
  foldr f b (BasisC x y) = f x (f y b) 
  foldr f b (BasisB x y) = f x (f y b) 
  foldr f b (EtaReduce x) = f x b
  foldr f b (CatRule _ c) = foldr f b c
  foldl _ b (VarRule _ _) = b
  foldl f b (AppRule _ x y) = f (f b x) y
  foldl f b (BasisK x) = f b x
  foldl _ b BasisI = b
  foldl f b (AbsRule _ _ x) = f b x
  foldl f b (BasisS x y) = f (f b x) y
  foldl f b (BasisC x y) = f (f b x) y 
  foldl f b (BasisB x y) = f (f b x) y 
  foldl f b (EtaReduce x) = f b x
  foldl f b (CatRule _ c) = foldl f b c
  foldMap _ (VarRule _ _) = mempty
  foldMap f (AppRule _ x y) = f x <> f y 
  foldMap f (BasisK x) = f x
  foldMap _ BasisI = mempty
  foldMap f (AbsRule _ _ x) = f x 
  foldMap f (BasisS x y) = f x <> f y 
  foldMap f (BasisC x y) = f x <> f y 
  foldMap f (BasisB x y) = f x <> f y 
  foldMap f (EtaReduce x) = f x
  foldMap f (CatRule _ c) = foldMap f c 


instance Traversable cat => Traversable (EliminationAlgebra var cat typ) where
  traverse _ (VarRule var typ) = pure $ VarRule var typ 
  traverse f (AppRule typ a b) = AppRule typ <$> f a <*> f b
  traverse f (BasisK a) = BasisK <$> f a
  traverse _ BasisI = pure BasisI 
  traverse f (AbsRule typ x a) = AbsRule typ x <$> f a
  traverse f (BasisS a b) = BasisS <$> f a <*> f b
  traverse f (BasisC a b) = BasisC <$> f a <*> f b
  traverse f (BasisB a b) = BasisB <$> f a <*> f b
  traverse f (EtaReduce a) = EtaReduce <$> f a
  traverse f (CatRule typ c) = CatRule typ <$> traverse f c 
  sequence = traverse identity

