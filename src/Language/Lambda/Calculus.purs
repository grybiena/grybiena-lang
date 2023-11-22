module Language.Lambda.Calculus where

import Prelude

import Control.Monad.State (State, evalState, get, put)
import Data.Eq (class Eq1, eq1)
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.Functor.Mu (Mu)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Matryoshka.Algebra (Algebra, AlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata, cataM)
import Prettier.Printer (DOC, text)

-- | Un-Fixed LambdaF 
data LambdaF var cat a =
    Abs var a
  | App a a
  | Var var
  | Cat (cat a)

type Lambda var cat = Mu (LambdaF var cat)

derive instance Generic (LambdaF var cat a) _

instance
  ( Eq var
  , Eq1 cat
  ) => Eq1 (LambdaF var cat) where
  eq1 (Abs i a) (Abs j b) = i == j && a == b
  eq1 (App ax bx) (App ay by) = ax == ay && bx == by
  eq1 (Var i) (Var j) = i == j
  eq1 (Cat a) (Cat b) = eq1 a b
  eq1 _ _ = false

instance
  ( Show var
  , Show (cat a)
  , Show a
  ) => Show (LambdaF var cat a) where
  show = genericShow

instance Functor cat => Functor (LambdaF var cat) where
  map f (Abs i a) = Abs i (f a)
  map f (App a b) = App (f a) (f b)
  map _ (Var i) = Var i
  map f (Cat c) = Cat (f <$> c)

instance Foldable cat => Foldable (LambdaF var cat) where
  foldr f b (Abs _ e) = f e b
  foldr f b (App x y) = f y (f x b)
  foldr _ b (Var _) = b
  foldr f b (Cat c) = foldr f b c
  foldl f b (Abs _ e) = f b e
  foldl f b (App x y) = f (f b y) x
  foldl _ b (Var _) = b
  foldl f b (Cat c) = foldl f b c
  foldMap f (Abs _ e) = f e
  foldMap f (App x y) = f x <> f y
  foldMap _ (Var _) = mempty
  foldMap f (Cat c) = foldMap f c


instance Traversable cat => Traversable (LambdaF var cat) where
  traverse f (Abs p e) = Abs p <$> (f e)
  traverse f (App a b) = App <$> f a <*> f b 
  traverse _ (Var v) = pure (Var v)
  traverse f (Cat c) = Cat <$> traverse f c
  sequence = traverse identity


freeIn :: forall var cat f .
            Ord var
         => Foldable cat
         => Recursive (f (LambdaF var cat)) (LambdaF var cat)
         => var -> f (LambdaF var cat) -> Boolean
freeIn v expr = v `Set.member` free expr


free :: forall var cat f .
        Ord var
     => Foldable cat
     => Recursive (f (LambdaF var cat)) (LambdaF var cat)
     => f (LambdaF var cat) -> Set var
free = cata freeVars 


freeVars :: forall var cat .
        Ord var
     => Foldable cat
     => Algebra (LambdaF var cat) (Set var)
freeVars (Abs v a) = Set.delete v a
freeVars (Var v) = Set.singleton v
freeVars (App a b) = a `Set.union` b 
freeVars (Cat c) = foldr Set.union Set.empty c

occursIn :: forall var cat f .
            Ord var
         => Foldable cat
         => Recursive (f (LambdaF var cat)) (LambdaF var cat)
         => var -> f (LambdaF var cat) -> Boolean
occursIn v expr = v `Set.member` universe expr

universe :: forall var cat f .
            Ord var
         => Foldable cat
         => Recursive (f (LambdaF var cat)) (LambdaF var cat)
         => f (LambdaF var cat) -> (Set var)
universe = cata allVars

allVars :: forall var cat .
        Ord var
     => Foldable cat
     => Algebra (LambdaF var cat) (Set var)
allVars (Abs v a) = Set.insert v a
allVars (Var v) = Set.singleton v
allVars (App a b) = a `Set.union` b 
allVars (Cat c) = foldr Set.union Set.empty c

replace :: forall var cat f .
           Eq var
        => Foldable cat
        => Recursive (f (LambdaF var cat)) (LambdaF var cat)
        => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
        => (var -> Maybe (f (LambdaF var cat)))
        -> f (LambdaF var cat)
        -> f (LambdaF var cat)
replace = cata <<< onVar


onVar :: forall var cat f .
        Eq var
     => Foldable cat
     => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
     => Recursive (f (LambdaF var cat)) (LambdaF var cat)
     => (var -> Maybe (f (LambdaF var cat)))
     -> Algebra (LambdaF var cat) (f (LambdaF var cat))
onVar replacement =
  case _ of
    Abs v a ->
      case project <$> replacement v of
        Just (Var v') -> abs v' a
        Just _ -> a
        _ -> abs v a
--    Abs v a | isJust (replacement v) -> a
--    Abs v a -> abs v a
    Var v -> maybe (var v) identity (replacement v)
    App a b -> app a b
    Cat c -> cat c

-- Variables can have added context (e.g. scope, skolem constant) which shadow removes
class Shadow var where
  shadow :: var -> var



replaceFree :: forall var cat f .
           Eq var
        => Foldable cat
        => Recursive (f (LambdaF var cat)) (LambdaF var cat)
        => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
        => Traversable cat
        => Shadow var
        => (var -> Maybe (f (LambdaF var cat)))
        -> f (LambdaF var cat)
        -> f (LambdaF var cat)
replaceFree r exp = evalState (cataM onFree exp) r


onFree :: forall var cat f .
        Eq var
     => Shadow var
     => Foldable cat
     => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
     => Recursive (f (LambdaF var cat)) (LambdaF var cat)
     => AlgebraM (State (var -> Maybe (f (LambdaF var cat)))) (LambdaF var cat) (f (LambdaF var cat))
onFree exp = do
  replacement <- get
  case exp of
    Abs v a -> do
       put (\x -> if shadow x == v then Nothing else replacement x)
       pure $ abs v a
    Var v -> pure $ maybe (var v) identity (replacement v)
    App a b -> pure $ app a b
    Cat c -> pure $ cat c




class PrettyVar i where
  prettyVar :: i -> DOC

instance PrettyVar String where
  prettyVar = text

instance PrettyVar Void where
  prettyVar = absurd

class PrettyVar var <= PrettyLambda var cat where
  prettyAbs :: var -> Lambda var cat -> DOC
  prettyApp :: Lambda var cat -> Lambda var cat -> DOC
  prettyCat :: cat (Lambda var cat) -> DOC


absMany :: forall t lam var cat .
           Corecursive lam (LambdaF var cat)
        => Functor t
        => Foldable t
        => t var -> lam -> lam
absMany ps = flip (foldr ($)) (abs <$> ps) 
 
abs :: forall lam var cat .
       Corecursive lam (LambdaF var cat)
    => var -> lam -> lam
abs p = embed <<< Abs p


app :: forall lam var cat .
       Corecursive lam (LambdaF var cat)
    => lam -> lam -> lam
app a = embed <<< App a


var :: forall lam var cat .
       Corecursive lam (LambdaF var cat)
    => var -> lam
var = embed <<< Var

cat :: forall lam var cat .
       Corecursive lam (LambdaF var cat)
    => cat lam -> lam 
cat = embed <<< Cat


