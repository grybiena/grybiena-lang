module Language.Lambda.Infer where

import Prelude

import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (LambdaF(..))
import Language.Lambda.Infer.Tree (class Reckon, reckon)
import Language.Void.Value (VoidF(..))
import Matryoshka.Algebra (Algebra)
import Matryoshka.Class.Corecursive (class Corecursive, embed)
import Matryoshka.Class.Recursive (class Recursive, project)
import Matryoshka.Fold (cata)



infer :: forall exp var cat m typ jujF juj.
         Recursive exp (LambdaF var cat)
      => Corecursive juj jujF
      => Monad m
      => Supply typ m
      => TypingContext var typ m
      => Rewrite typ m
      => AbsRule var typ jujF juj
      => AppRule jujF juj m
      => VarRule var typ (jujF juj)
      => CatRule cat (m juj)
      => Reckon juj m
      => exp -> m juj
infer = cata judge

judge :: forall var cat m typ jujF juj.
         Monad m
      => Corecursive juj jujF
      => Supply typ m
      => TypingContext var typ m
      => Rewrite typ m
      => AbsRule var typ jujF juj
      => AppRule jujF juj m
      => VarRule var typ (jujF juj)
      => CatRule cat (m juj)
      => Reckon juj m
      => Algebra (LambdaF var cat) (m juj) 
judge lam = reckon
  case lam of
    Abs binding inferBody -> do
       tyBind <- fresh
       makeAssumption binding tyBind
       tyBody <- inferBody
       tyBind' <- applyCurrentSubstitution tyBind
       pure $ embed $ absRule binding tyBind' tyBody
    App f a -> embed <$> (join $ appRule <$> f <*> a)
    Var v -> embed <<< varRule v <$> (askEnvironment v >>= applyCurrentSubstitution)
    Cat c -> catRule c

class AbsRule var typ jujF juj where
  absRule :: var -> typ -> juj -> jujF juj

class Corecursive juj jujF <= AppRule jujF juj m where
  appRule :: juj -> juj -> m (jujF juj)

class VarRule var typ juj where
  varRule :: var -> typ -> juj

class CatRule cat inf where
  catRule :: cat inf -> inf


instance CatRule VoidF a where 
  catRule (VoidF v) = absurd v

 
instance
  ( Monad m
  , Corecursive juj jujF
  , Recursive juj jujF
  , TypingJudgement exp typ jujF juj
  , TypingApplication typ jujF juj
  , Rewrite typ m
  , Unify typ m
  ) => AppRule jujF juj m where
  appRule f a = do
    let _ /\ arrTy = judgement $ project f
    arrArg /\ arrRet <- unifyWithArrow arrTy
    let _ /\ argTy = judgement $ project a
    void $ unify argTy arrArg 
    appTy <- applyCurrentSubstitution arrRet
    pure $ typingApplication f a appTy

--------------

class Supply :: Type -> (Type -> Type) -> Constraint
class Supply typ m where
  fresh :: m typ

class TypingContext var typ m | var -> typ where
  makeAssumption :: var -> typ -> m Unit
  askEnvironment :: var -> m typ

class Unify typ m where
  unify :: typ -> typ -> m typ
  unifyWithArrow :: typ -> m (typ /\ typ)

class Corecursive juj jujF <= TypingJudgement exp typ jujF juj | juj -> exp, juj -> typ where 
  judgement :: jujF juj -> exp /\ typ

class Corecursive juj jujF <= TypingApplication typ jujF juj where
  typingApplication :: juj -> juj -> typ -> jujF juj

class Substitution var typ m where
  substitute :: var -> typ -> m Unit

class Rewrite typ m where
  applyCurrentSubstitution :: typ -> m typ


