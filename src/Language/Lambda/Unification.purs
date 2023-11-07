module Language.Lambda.Unification where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Except.Trans (class MonadThrow)
import Control.Monad.State (class MonadState, State, get, modify, modify_, runState)
import Data.Either (Either)
import Data.Foldable (class Foldable)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (LambdaF(..), abs, app, cat, occursIn, replace, var)
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
  , Foldable cat
  , Functor m
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , Eq var
  ) => Rewrite (f (LambdaF var cat)) m where
  rewrite expr = flip replace expr <$> substitution 

class Context var typ m | var -> typ where
  assume :: var -> typ -> m Unit
  require :: var -> m typ

class NotInScopeError var err where
  notInScopeError :: var -> err
 
class Unification typ m where
  unify :: typ -> typ -> m typ

class UnificationError typ err where
  unificationError :: typ -> typ -> err

class InfiniteTypeError var typ err where
  infiniteTypeError :: var -> typ -> err

instance
  ( Monad m
  , Fresh var m 
  , Eq var
  , Substitute var cat f m 
  , Rewrite (f (LambdaF var cat)) m 
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Corecursive (f (LambdaF var cat)) (LambdaF var cat)
  , Unification (cat (f (LambdaF var cat))) m
  , UnificationError (f (LambdaF var cat)) err
  , MonadThrow err m
  ) => Unification (f (LambdaF var cat)) m where
  unify ta tb = do
     case project ta /\ project tb of
       Var a /\ Var b | a == b -> pure ta
       Var a /\ _ -> substitute a tb *> pure tb
       _ /\ Var b -> substitute b ta *> pure ta
       Abs ab aa /\ Abs bb ba -> do
         qv <- fresh
         let qty :: f (LambdaF var cat)
             qty = var qv
         substitute ab qty
         substitute bb qty
         ar <- rewrite aa
         br <- rewrite ba
         abs qv <$> unify ar br
       App ab aa /\ App bb ba -> do
         app <$> unify ab bb <*> unify aa ba
       Cat ca /\ Cat cb -> cat <$> unify ca cb
       _ -> throwError $ unificationError ta tb


type TypingContext var f var' cat' =
  { nextVar :: Int
  , typingAssumptions :: Map var (f (LambdaF var' cat')) 
  , currentSubstitution :: Map var' (f (LambdaF var' cat'))
  }

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
  ( MonadState (TypingContext var f var' cat') m 
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
  , Foldable cat'
  , Fresh var' m
  , MonadState (TypingContext var f var' cat') m
  , Recursive (f (LambdaF var' cat')) (LambdaF var' cat')
  , Corecursive (f (LambdaF var' cat')) (LambdaF var' cat')
  , InfiniteTypeError var' (f (LambdaF var' cat')) err
  , Unification (cat' (f (LambdaF var' cat'))) m
  , UnificationError (f (LambdaF var' cat')) err
  , MonadThrow err m
  ) => Substitute var' cat' f m where
  substitute v t' = do
     t <- rewrite t'
     when (v `occursIn` t) $ throwError $ infiniteTypeError v t 
     u <- rewrite (var v)
     case project u of
        Var v' | v' == v -> pure unit 
        _ -> void $ unify u t
     let subNew = replace (\x -> if x == v then Just t else Nothing)
     modify_ (\st -> st {
                currentSubstitution = Map.insert v t (subNew <$> st.currentSubstitution)
              })
  substitution = do
    st <- get
    pure $ flip Map.lookup st.currentSubstitution


