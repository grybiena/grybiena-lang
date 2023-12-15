module Language.Lambda.Calculus where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail)
import Control.Monad.State (State, evalState, get, put)
import Data.Eq (class Eq1, eq1)
import Data.Foldable (class Foldable, elem, foldMap, foldl, foldr)
import Data.Functor.Mu (Mu)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), filter)
import Data.List as List
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Matryoshka.Algebra (Algebra, AlgebraM)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata, cataM)
import Prettier.Printer (DOC, text)

-- | Un-Fixed LambdaF 
data LambdaF abs var cat a =
    Abs abs a
  | App a a
  | Var var
  | Cat (cat a)

type TermF var = LambdaF var var
type PatternF var = LambdaF Void var

type Lambda abs var cat = Mu (LambdaF abs var cat)

derive instance Generic (LambdaF abs var cat a) _

instance
  ( Eq abs
  , Eq var
  , Eq1 cat
  ) => Eq1 (LambdaF abs var cat) where
  eq1 (Abs i a) (Abs j b) = i == j && a == b
  eq1 (App ax bx) (App ay by) = ax == ay && bx == by
  eq1 (Var i) (Var j) = i == j
  eq1 (Cat a) (Cat b) = eq1 a b
  eq1 _ _ = false

instance
  ( Show abs
  , Show var
  , Show (cat a)
  , Show a
  ) => Show (LambdaF abs var cat a) where
  show = genericShow

instance Functor cat => Functor (LambdaF abs var cat) where
  map f (Abs i a) = Abs i (f a)
  map f (App a b) = App (f a) (f b)
  map _ (Var i) = Var i
  map f (Cat c) = Cat (f <$> c)

instance Foldable cat => Foldable (LambdaF abs var cat) where
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


instance Traversable cat => Traversable (LambdaF abs var cat) where
  traverse f (Abs p e) = Abs p <$> (f e)
  traverse f (App a b) = App <$> f a <*> f b 
  traverse _ (Var v) = pure (Var v)
  traverse f (Cat c) = Cat <$> traverse f c
  sequence = traverse identity



freeIn :: forall abs var cat f .
            Ord var
         => Foldable cat
         => Recursive (f (LambdaF abs var cat)) (LambdaF abs var cat)
         => FreeVars abs var cat
         => var -> f (LambdaF abs var cat) -> Boolean
freeIn v expr = v `elem` free expr


free :: forall exp abs var cat .
        Ord var
     => Foldable cat
     => Recursive exp (LambdaF abs var cat)
     => FreeVars abs var cat
     => exp -> List var
free = cata freeVars 

freeTyped :: forall typ var cat .
             Ord var
          => Foldable cat
          => Functor cat
          => Cofree (LambdaF var var cat) typ -> List (var /\ typ)
freeTyped t =
  case head t /\ tail t of
    (ty /\ Var v) -> List.singleton (v /\ ty)
    (_ /\ App a b) -> freeTyped a <> freeTyped b
    (_ /\ Abs x b) -> filter (not <<< eq x <<< fst) $ freeTyped b
    (_ /\ Cat c) -> foldl append Nil (freeTyped <$> c)



class FreeVars abs var cat where
  freeVars :: Algebra (LambdaF abs var cat) (List var) 

instance
  ( Ord var
  , Foldable cat
  ) => FreeVars Void var cat where
  freeVars (Abs _ a) = a
  freeVars (Var v) = List.singleton v
  freeVars (App a b) = List.nub (a <> b) 
  freeVars (Cat c) = foldl append Nil c
else
instance
  ( Ord var
  , Foldable cat
  , Recursive (f (LambdaF Void var pat)) (LambdaF Void var pat)
  , Foldable pat
  ) => FreeVars (f (LambdaF Void var pat)) var cat where
  freeVars (Abs v a) = List.difference a (free v)
  freeVars (Var v) = List.singleton v
  freeVars (App a b) = List.nub (a <> b) 
-- TODO this is wrong since we don't account for bound patterns capturing
-- variables...
  freeVars (Cat c) = foldl append Nil c
else
instance
  ( Ord var
  , Foldable cat
  ) => FreeVars var var cat where
  freeVars (Abs v a) = List.delete v a 
  freeVars (Var v) = List.singleton v
  freeVars (App a b) = List.nub (a <> b) 
  freeVars (Cat c) = foldl append Nil c


occursIn :: forall exp abs var cat .
            Ord var
         => Foldable cat
         => Recursive exp (LambdaF abs var cat)
         => AllVars abs var cat
         => var -> exp -> Boolean
occursIn v expr = v `Set.member` universe expr

universe :: forall exp abs var cat .
            Ord var
         => Foldable cat
         => Recursive exp (LambdaF abs var cat)
         => AllVars abs var cat
         => exp -> (Set var)
universe = cata allVars

class AllVars abs var cat where
  allVars :: Algebra (LambdaF abs var cat) (Set var) 

instance
  ( Ord var
  , Foldable cat
  ) => AllVars Void var cat where
  allVars (Abs _ a) = a
  allVars (Var v) = Set.singleton v
  allVars (App a b) = a `Set.union` b 
  allVars (Cat c) = foldr Set.union Set.empty c
else
instance
  ( Ord var
  , Foldable cat
  , Foldable pat
  , Recursive (f (LambdaF Void var pat)) (LambdaF Void var pat)
  ) => AllVars (f (LambdaF Void var pat)) var cat where
  allVars (Abs v a) = Set.union (universe v) a
  allVars (Var v) = Set.singleton v
  allVars (App a b) = a `Set.union` b 
  allVars (Cat c) = foldr Set.union Set.empty c
else
instance
  ( Ord var
  , Foldable cat
  ) => AllVars var var cat where
  allVars (Abs v a) = Set.insert v a
  allVars (Var v) = Set.singleton v
  allVars (App a b) = a `Set.union` b 
  allVars (Cat c) = foldr Set.union Set.empty c



replace :: forall var cat f .
           Eq var
        => Foldable cat
        => Recursive (f (LambdaF var var cat)) (LambdaF var var cat)
        => Corecursive (f (LambdaF var var cat)) (LambdaF var var cat)
        => (var -> Maybe (f (LambdaF var var cat)))
        -> f (LambdaF var var cat)
        -> f (LambdaF var var cat)
replace = cata <<< onVar


onVar :: forall var cat f .
        Eq var
     => Foldable cat
     => Corecursive (f (LambdaF var var cat)) (LambdaF var var cat)
     => Recursive (f (LambdaF var var cat)) (LambdaF var var cat)
     => (var -> Maybe (f (LambdaF var var cat)))
     -> Algebra (LambdaF var var cat) (f (LambdaF var var cat))
onVar replacement =
  case _ of
    Abs v a ->
      case project <$> replacement v of
        Just (Var v') -> abs v' a
        Just _ -> a
        _ -> abs v a
    Var v -> maybe (var v) identity (replacement v)
    App a b -> app a b
    Cat c -> cat c

-- Variables can have added context (e.g. scope, skolem constant) which shadow removes
class Shadow var where
  shadow :: var -> var



replaceFree :: forall var cat f .
           Eq var
        => Foldable cat
        => Recursive (f (LambdaF var var cat)) (LambdaF var var cat)
        => Corecursive (f (LambdaF var var cat)) (LambdaF var var cat)
        => Traversable cat
        => Shadow var
        => (var -> Maybe (f (LambdaF var var cat)))
        -> f (LambdaF var var cat)
        -> f (LambdaF var var cat)
replaceFree r exp = evalState (cataM onFree exp) r


onFree :: forall var cat f .
        Eq var
     => Shadow var
     => Foldable cat
     => Corecursive (f (LambdaF var var cat)) (LambdaF var var cat)
     => Recursive (f (LambdaF var var cat)) (LambdaF var var cat)
     => AlgebraM (State (var -> Maybe (f (LambdaF var var cat)))) (LambdaF var var cat) (f (LambdaF var var cat))
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

class PrettyVar var <= PrettyLambda abs var cat where
  prettyAbs :: abs -> Lambda abs var cat -> DOC
  prettyApp :: Lambda abs var cat -> Lambda abs var cat -> DOC
  prettyCat :: cat (Lambda abs var cat) -> DOC


absMany :: forall t lam abs var cat .
           Corecursive lam (LambdaF abs var cat)
        => Functor t
        => Foldable t
        => t abs -> lam -> lam
absMany ps = flip (foldr ($)) (abs <$> ps) 

appMany :: forall t lam abs var cat .
            Corecursive lam (LambdaF abs var cat)
        => Functor t
        => Foldable t
        => lam -> t lam -> lam
appMany f args = foldl app f args
          
 
abs :: forall lam abs var cat .
       Corecursive lam (LambdaF abs var cat)
    => abs -> lam -> lam
abs p = embed <<< Abs p


app :: forall lam abs var cat .
       Corecursive lam (LambdaF abs var cat)
    => lam -> lam -> lam
app a = embed <<< App a


var :: forall lam abs var cat .
       Corecursive lam (LambdaF abs var cat)
    => var -> lam
var = embed <<< Var

cat :: forall lam abs var cat .
       Corecursive lam (LambdaF abs var cat)
    => cat lam -> lam 
cat = embed <<< Cat

flat :: forall exp typ abs var cat.
        Functor cat
     => Recursive exp (LambdaF abs var cat)
     => Corecursive exp (LambdaF abs var cat)
     => Cofree (LambdaF abs var cat) typ 
     -> exp 
flat c = embed (flat <$> tail c)


