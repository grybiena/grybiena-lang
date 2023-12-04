module Language.Lambda.Elimination.Algebra where

-- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis

import Prelude

import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.Traversable (class Traversable, traverse)

-- Annotated with rules described here https://en.wikipedia.org/wiki/Combinatory_logic#Combinators_B,_C
data EliminationAlgebra var cat t =
    VarRule var     -- 1. T[x] ⇒ x 
  | AppRule t t     -- 2. T[(E₁ E₂)] ⇒ (T[E₁] T[E₂])
  | BasisK t        -- 3. T[λx.E] ⇒ (K T[E]) (if x is not free in E)
  | BasisI          -- 4. T[λx.x] ⇒ I
  | AbsRule var t   -- 5. T[λx.λy.E] ⇒ T[λx.T[λy.E]] (if x is free in E)
  | BasisS var t t  -- 6. T[λx.(E₁ E₂)] ⇒ (S T[λx.E₁] T[λx.E₂]) (if x is free in both E₁ and E₂)
  | BasisC var t t  -- 7. T[λx.(E₁ E₂)] ⇒ (C T[λx.E₁] T[E₂]) (if x is free in E₁ but not E₂)
  | BasisB var t t  -- 8. T[λx.(E₁ E₂)] ⇒ (B T[E₁] T[λx.E₂]) (if x is free in E₂ but not E₁)
  | EtaReduce t     -- eta reduction. T[λx.a x] ⇒ T[a]
  | CatRule (cat t) -- cat reduction (by cat traversal)

instance Functor cat => Functor (EliminationAlgebra var cat) where
  map _ (VarRule var) = VarRule var
  map f (AppRule a b) = AppRule (f a) (f b)
  map f (BasisK a) = BasisK (f a)
  map _ BasisI = BasisI
  map f (AbsRule x a) = AbsRule x (f a)
  map f (BasisS x a b) = BasisS x (f a) (f b)
  map f (BasisC x a b) = BasisC x (f a) (f b)
  map f (BasisB x a b) = BasisB x (f a) (f b)
  map f (EtaReduce a) = EtaReduce (f a)
  map f (CatRule c) = CatRule (f <$> c)


 
instance Foldable cat => Foldable (EliminationAlgebra var cat) where
  foldr _ b (VarRule _) = b
  foldr f b (AppRule x y) = f x (f y b) 
  foldr f b (BasisK x) = f x b
  foldr _ b BasisI = b
  foldr f b (AbsRule _ x) = f x b
  foldr f b (BasisS _ x y) = f x (f y b) 
  foldr f b (BasisC _ x y) = f x (f y b) 
  foldr f b (BasisB _ x y) = f x (f y b) 
  foldr f b (EtaReduce x) = f x b
  foldr f b (CatRule c) = foldr f b c
  foldl _ b (VarRule _) = b
  foldl f b (AppRule x y) = f (f b x) y
  foldl f b (BasisK x) = f b x
  foldl _ b BasisI = b
  foldl f b (AbsRule _ x) = f b x
  foldl f b (BasisS _ x y) = f (f b x) y
  foldl f b (BasisC _ x y) = f (f b x) y 
  foldl f b (BasisB _ x y) = f (f b x) y 
  foldl f b (EtaReduce x) = f b x
  foldl f b (CatRule c) = foldl f b c
  foldMap _ (VarRule _) = mempty
  foldMap f (AppRule x y) = f x <> f y 
  foldMap f (BasisK x) = f x
  foldMap _ BasisI = mempty
  foldMap f (AbsRule _ x) = f x 
  foldMap f (BasisS _ x y) = f x <> f y 
  foldMap f (BasisC _ x y) = f x <> f y 
  foldMap f (BasisB _ x y) = f x <> f y 
  foldMap f (EtaReduce x) = f x
  foldMap f (CatRule c) = foldMap f c 


instance Traversable cat => Traversable (EliminationAlgebra var cat) where
  traverse _ (VarRule var) = pure (VarRule var)
  traverse f (AppRule a b) = AppRule <$> f a <*> f b
  traverse f (BasisK a) = BasisK <$> f a
  traverse _ BasisI = pure BasisI 
  traverse f (AbsRule x a) = AbsRule x <$> f a
  traverse f (BasisS x a b) = BasisS x <$> f a <*> f b
  traverse f (BasisC x a b) = BasisC x <$> f a <*> f b
  traverse f (BasisB x a b) = BasisB x <$> f a <*> f b
  traverse f (EtaReduce a) = EtaReduce <$> f a
  traverse f (CatRule c) = CatRule <$> traverse f c 
  sequence = traverse identity

