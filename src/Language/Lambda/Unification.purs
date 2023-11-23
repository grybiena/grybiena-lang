module Language.Lambda.Unification where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Except.Trans (class MonadThrow)
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
import Language.Lambda.Calculus (class Shadow, LambdaF(..), occursIn, replace, replaceFree, shadow, universe, var)
import Matryoshka.Class.Corecursive (class Corecursive)
import Matryoshka.Class.Recursive (class Recursive, project)

class Enumerable k where
  fromInt :: Int -> k

class Monad m <= Fresh typ m where
  fresh :: m typ

class Substitute var cat f m where
  substitute :: var -> f (LambdaF var cat) -> m Unit
  substitution :: m (var -> Maybe (f (LambdaF var cat)))

class Rewrite typ m where
  rewrite :: typ -> m typ

instance
  ( Substitute var cat f m
  , Traversable cat
  , Shadow var
  , Functor m
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , Eq var
  ) => Rewrite (f (LambdaF var cat)) m where
  rewrite expr = flip replaceFree expr <$> substitution 

class Context var typ m | var -> typ where
  assume :: var -> typ -> m Unit
  require :: var -> m typ

class NotInScopeError var err where
  notInScopeError :: var -> err
 
class Unify a b m where
  unify :: a -> b-> m Unit

class UnificationError typ err where
  unificationError :: typ -> typ -> err

class InfiniteTypeError var typ err | typ -> err where
  infiniteTypeError :: var -> typ -> err

newtype Skolem = Skolem Int
derive newtype instance Show Skolem
derive newtype instance Ord Skolem
derive newtype instance Eq Skolem

instance Enumerable Skolem where
  fromInt = Skolem

class Skolemize f var cat where
  skolemize :: var -> Skolem -> f (LambdaF var cat) -> f (LambdaF var cat)

instance
  ( Monad m
  , Fresh Int m 
  , Fresh var m
  , Eq var
  , Substitute var cat f m 
  , Rewrite (f (LambdaF var cat)) m 
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , Unify (cat (f (LambdaF var cat))) (cat (f (LambdaF var cat))) m
  , Unify var (f (LambdaF var cat)) m
  , UnificationError (f (LambdaF var cat)) err
  , Skolemize f var cat
  , MonadThrow err m
  ) => Unify (f (LambdaF var cat)) (f (LambdaF var cat)) m where
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
       _ -> throwError $ unificationError ta tb


type TypingContext var f var' cat' =
  { nextVar :: Int
  , typingAssumptions :: Map var (f (LambdaF var' cat')) 
  , currentSubstitution :: Map var' (f (LambdaF var' cat'))
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
  , Corecursive (f (LambdaF var' cat')) (LambdaF var' cat')
  ) => Fresh (f (LambdaF var' cat')) m where
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
  , NotInScopeError var err
  , MonadState (TypingContext var f var' cat') m
  , MonadThrow err m
  ) => Context var (f (LambdaF var' cat')) m where
  assume v t =
     modify_ (\st -> st {
       typingAssumptions = Map.insert v t st.typingAssumptions
       })
  require v = do
    st <- get
    case Map.lookup v st.typingAssumptions of
      Just t -> pure t
      Nothing -> throwError $ notInScopeError v


instance
  ( Ord var'
  , Shadow var'
  , Traversable cat'
  , Fresh var' m
  , Skolemize f var' cat'
  , MonadState (TypingContext var f var' cat') m
  , Recursive (f (LambdaF var' cat')) (LambdaF var' cat')
  , Corecursive (f (LambdaF var' cat')) (LambdaF var' cat')
  , InfiniteTypeError var' (f (LambdaF var' cat')) err
  , Unify (cat' (f (LambdaF var' cat'))) (cat' (f (LambdaF var' cat'))) m
  , Unify var' (f (LambdaF var' cat')) m
  , UnificationError (f (LambdaF var' cat')) err
  , MonadThrow err m
  , Shadow var' -- TODO is it safe to only consider shadows?
  ) => Substitute var' cat' f m where
  substitute v t' = do
     t <- rewrite t'
     -- TODO is this a strong enough check?
     -- i.e. is rewriting { a ~> forall a. a -> a } sound or going to result in doom?
     when (v `occursIn` t) $ throwError $ infiniteTypeError v t 
     u <- rewrite (var v :: f (LambdaF var' cat'))
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
    => Recursive (f (LambdaF var cat)) (LambdaF var cat)
    => Corecursive (f (LambdaF var cat)) (LambdaF var cat)
    => Fresh var m
    => f (LambdaF var cat) -> m (f (LambdaF var cat))
renameFresh t = do
  r <- flip traverse (fromFoldable $ Set.map shadow $ universe t) $ \v -> do
    x <- fresh
    pure (v /\ (var x :: f (LambdaF var cat)))
  let re = Map.fromFoldable r
  pure $ replace (\v -> Map.lookup (shadow v) re) t


