module Language.Lambda.Unification where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State (class MonadState, State, StateT, get, modify, modify_, runState, runStateT)
import Data.Either (Either)
import Data.Foldable (class Foldable)
import Data.List (fromFoldable)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Traversable (class Traversable, traverse)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (class AllVars, class Shadow, LambdaF(..), TermF, occursIn, replace, replaceFree, shadow, universe, var)
import Language.Lambda.Unification.Error (class ThrowUnificationError, unificationError)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)

class Enumerable k where
  fromInt :: Int -> k

class Monad m <= Fresh typ m where
  fresh :: m typ

class Substitute var cat f m where
  substitute :: var -> f (TermF var cat) -> m Unit
  substitution :: m (var -> Maybe (f (TermF var cat)))

class Rewrite typ m where
  rewrite :: typ -> m typ

instance
  ( Substitute var cat f m
  , Traversable cat
  , Shadow var
  , Functor m
  , Recursive (f (TermF var cat)) (TermF var cat)
  , Corecursive (f (TermF var cat)) (TermF var cat)
  , Eq var
  ) => Rewrite (f (TermF var cat)) m where
  rewrite expr = flip replace expr <$> substitution 

class Context var typ m | var -> typ where
  assume :: var -> typ -> m Unit
  require :: var -> m typ

class Monad m <= NotInScopeError var m where
  notInScopeError :: forall a. var -> m a
 
class Unify a b m where
  unify :: a -> b-> m Unit

class Monad m <= InfiniteTypeError var typ m where
  infiniteTypeError :: forall a. var -> typ -> m a 

newtype Skolem = Skolem Int
derive newtype instance Show Skolem
derive newtype instance Ord Skolem
derive newtype instance Eq Skolem

instance Enumerable Skolem where
  fromInt = Skolem

class Skolemize f var cat where
  skolemize :: var -> Skolem -> f (TermF var cat) -> f (TermF var cat)

instance
  ( Monad m
  , Fresh Int m 
  , Fresh var m
  , Eq var
  , Substitute var cat f m 
  , Rewrite (f (TermF var cat)) m 
  , Recursive (f (TermF var cat)) (TermF var cat)
  , Corecursive (f (TermF var cat)) (TermF var cat)
  , Unify (cat (f (TermF var cat))) (cat (f (TermF var cat))) m
  , Unify var (f (TermF var cat)) m
  , ThrowUnificationError (f (TermF var cat)) m
  , Skolemize f var cat
  ) => Unify (f (TermF var cat)) (f (TermF var cat)) m where
  unify ta tb = do
     case project ta /\ project tb of
       Var v /\ _ -> unify v tb
       _ /\ Var v -> unify v ta 
       Abs ab aa /\ Abs bb ba -> do
         sko <- fresh
         let ska = skolemize ab sko aa
             skb = skolemize bb sko ba
         unify ska skb
       Abs ab aa /\ _ -> do
         sko <- fresh
         let ska = skolemize ab sko aa
         unify ska tb
       _ /\ Abs _ _ -> unify tb ta
       App ab aa /\ App bb ba -> do
         unify ab bb *> unify aa ba
       Cat ca /\ Cat cb -> unify ca cb
       _ -> unificationError ta tb


type TypingContext var f var' cat' =
  { nextVar :: Int
  , typingAssumptions :: Map var (f (TermF var' cat')) 
  , currentSubstitution :: Map var' (f (TermF var' cat'))
  }


runUnificationT :: forall var f var' cat' err a m.
                  ExceptT err (StateT (TypingContext var f var' cat') m) a
               ->  m (Either err a /\ TypingContext var f var' cat')
runUnificationT = flip runStateT { nextVar: 0
                               , typingAssumptions: Map.empty
                               , currentSubstitution: Map.empty
                               } <<< runExceptT


runUnification :: forall var f var' cat' err a.
                  ExceptT err (State (TypingContext var f var' cat')) a
               -> Either err a /\ TypingContext var f var' cat'
runUnification = flip runState { nextVar: 0
                               , typingAssumptions: Map.empty
                               , currentSubstitution: Map.empty
                               } <<< runExceptT

instance MonadState (TypingContext var f var' cat') m => Fresh Int m where
  fresh = do
    st <- modify (\st -> st {
      nextVar = st.nextVar + 1
    })
    pure st.nextVar
else
instance
  ( MonadState (TypingContext var f var' cat') m 
  , Enumerable var'
  , Corecursive (f (TermF var' cat')) (TermF var' cat')
  ) => Fresh (f (TermF var' cat')) m where
  fresh = var <<< fromInt <$> fresh
else
instance
  ( Monad m
  , Fresh Int m
  , Enumerable var'
  ) => Fresh var' m where
  fresh = fromInt <$> fresh



instance
  ( Monad m
  , Ord var
  , NotInScopeError var m
  , MonadState (TypingContext var f var' cat') m
  ) => Context var (f (TermF var' cat')) m where
  assume v t =
     modify_ (\st -> st {
       typingAssumptions = Map.insert v t st.typingAssumptions
       })
  require v = do
    st <- get
    case Map.lookup v st.typingAssumptions of
      Just t -> pure t
      Nothing -> notInScopeError v


instance
  ( Ord var'
  , Shadow var'
  , Traversable cat'
  , Fresh var' m
  , Skolemize f var' cat'
  , MonadState (TypingContext var f var' cat') m
  , Recursive (f (TermF var' cat')) (TermF var' cat')
  , Corecursive (f (TermF var' cat')) (TermF var' cat')

  , Unify (cat' (f (TermF var' cat'))) (cat' (f (TermF var' cat'))) m
  , Unify var' (f (TermF var' cat')) m
  , ThrowUnificationError (f (TermF var' cat')) m 
  , InfiniteTypeError var' (f (TermF var' cat')) m
  , AllVars var' var' cat' 
  , Shadow var' -- TODO is it safe to only consider shadows?
  ) => Substitute var' cat' f m where
  substitute v t' = do
     t <- rewrite t'
     when (v `occursIn` t) $ infiniteTypeError v t 
     u <- rewrite (var v :: f (TermF var' cat'))
     case project u of
        Var v' | v' == v -> pure unit 
        _ -> void $ unify u t
     let subNew = replaceFree (\x -> if x == v then Just t else Nothing)
     modify_ (\st -> st {
                currentSubstitution = Map.insert (shadow v) t (subNew <$> st.currentSubstitution)
              })
  substitution = do
    st <- get
    pure $ flip Map.lookup st.currentSubstitution <<< shadow

-- | Rename all of the bindings and variables with fresh ones
-- without incurring any substitutions (the new variables will be unique to the term)
renameFresh :: forall f var cat m.
       Monad m
    => Ord var
    => Shadow var
    => Foldable cat
    => Recursive (f (TermF var cat)) (TermF var cat)
    => Corecursive (f (TermF var cat)) (TermF var cat)
    => Fresh var m
    => AllVars var var cat
    => f (TermF var cat) -> m (f (TermF var cat))
renameFresh t = do
  r <- flip traverse (fromFoldable $ Set.map shadow $ universe t) $ \v -> do
    x <- fresh
    pure (v /\ (var x :: f (TermF var cat)))
  let re = Map.fromFoldable r
  pure $ replace (\v -> Map.lookup (shadow v) re) t


