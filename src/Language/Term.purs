module Language.Term where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (class MonadState)
import Data.Array (replicate)
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable, foldr)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (class Traversable, traverse, traverse_)
import Data.Tuple (uncurry)
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, class Shadow, Lambda, LambdaF(..), app, cat, prettyVar, replaceFree, var)
import Language.Lambda.Inference (class ArrowObject, class Inference, class IsStar, arrow, infer, unifyWithArrow)
import Language.Lambda.Reduction (class Composition, class Reduction)
import Language.Lambda.Unification (class Enumerable, class Fresh, class InfiniteTypeError, class NotInScopeError, class Skolemize, class UnificationError, class Unify, Skolem, TypingContext, assume, fresh, fromInt, rewrite, substitute, unificationError, unify)
import Language.Native (class NativeValue, Native(..))
import Language.Term.LetRec (recSeq)
import Matryoshka.Class.Recursive (project)
import Prettier.Printer (stack, text, (<+>), (</>))
import Pretty.Printer (class Pretty, pretty, prettyPrint)
import Prim (Boolean, Int, Number, Record, String)

type Term = Lambda Var TT


data TT a =
    Star Int
  | Arrow
  | LetRec (Map Var a) a
  | TypeAnnotation a Term
  | TypeLit Term
  | Native (Native Term)

derive instance Generic (TT a) _

instance NativeValue Mu Var TT where
  native = cat <<< Native

instance (Pretty a, Show a) => Show (TT a) where
  show (TypeAnnotation a t) = "TypeAnnotation " <> show a <> " " <> show t
  show e = genericShow e

instance IsStar Mu Var TT where
  isStar t = case project t of
               Cat (Star _) -> true
               _ -> false

instance Functor TT where
  map _ Arrow = Arrow
  map _ (Star i) = Star i
  map f (LetRec bs a) = LetRec (f <$> bs) (f a)
  map f (TypeAnnotation a t) = TypeAnnotation (f a) t
  map _ (TypeLit t) = TypeLit t
  map _ (Native n) = Native n 

instance Traversable TT where
  traverse _ Arrow = pure Arrow
  traverse _ (Star i) = pure (Star i)
  traverse f (LetRec bs a) = LetRec <$> (traverse f bs) <*> f a
  traverse f (TypeAnnotation a t) = flip TypeAnnotation t <$> f a
  traverse _ (TypeLit t) = pure $ TypeLit t
  traverse _ (Native n) = pure $ Native n 
  sequence = traverse identity

instance Skolemize Mu Var TT where
  skolemize (Scoped i s) k = replaceFree (\x -> if x == Ident i then Just (var (Skolemized i s k)) else Nothing) 
  -- TODO error if the Var is not Scoped
  skolemize _ _ = identity

instance Eq a => Eq (TT a) where
  eq = genericEq

instance Eq1 TT where
  eq1 = genericEq

instance Foldable TT where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

newtype Scope = Scope Int
derive newtype instance Show Scope
derive newtype instance Ord Scope
derive newtype instance Eq Scope


data Var =
    Ident Ident
  | Scoped Ident Scope 
  | Skolemized Ident Scope Skolem


derive instance Generic Var _
instance Show Var where
  show = genericShow
instance Ord Var where
  compare = genericCompare
instance Eq Var where
  eq = genericEq

instance Pretty Var where
  pretty (Ident i) = pretty i
  pretty (Scoped i s) = pretty i <> text (":" <> show s)
  pretty (Skolemized i s k) = pretty i <> text (":" <> show s) <> text (":" <>show k)

instance Shadow Var where
  shadow (Ident i) = Ident i
  shadow (Scoped i _) = Ident i
  shadow (Skolemized i _ _) = Ident i

instance PrettyVar Var where
  prettyVar = pretty

data Ident =
    TypeVar String
  | TermVar String

derive instance Generic Ident _
instance Show Ident where
  show = genericShow
instance Ord Ident where
  compare = genericCompare
instance Eq Ident where
  eq = genericEq

instance Pretty Ident where
  pretty (TypeVar v) = text v
  pretty (TermVar v) = text v

isTypeIdent :: Ident -> Boolean
isTypeIdent (TypeVar _) = true
isTypeIdent _ = false

isTypeVar :: Var -> Boolean
isTypeVar (Ident i) = isTypeIdent i
isTypeVar (Scoped i _) = isTypeIdent i
isTypeVar (Skolemized i _ _) = isTypeIdent i

instance PrettyLambda Var TT where
  prettyAbs i a | isTypeVar i = text "(forall " <> prettyVar i <+> text "." <+> pretty a <> text ")"
  prettyAbs i a = text "(\\" <> prettyVar i <+> text "->" <+> pretty a <> text ")"
  prettyApp (In (App (In (Cat Arrow)) a)) b = text "(" <> pretty a <+> text "->" <+> pretty b <> text ")"
  prettyApp f a = text "(" <> pretty f <+> pretty a <> text ")"
  prettyCat Arrow = text "->"
  prettyCat (Star i) = text (fromCharArray $ replicate i '*')
  prettyCat (LetRec bs a) =
    (text "let" <+> prettyBinds)
                </> (text "in" <+> pretty a)
    where
      -- TODO pull out function args instead of pretty printing lambdas
      prettyBinds = stack (prettyBind <$> Map.toUnfoldable bs)
      prettyBind (v /\ b) = pretty v <+> text "=" <+> pretty b      
  prettyCat (TypeAnnotation v t) = text "(" <> pretty v <+> text "::" <+> pretty t <> text ")"
  prettyCat (TypeLit a) = text "@" <> pretty a
  prettyCat (Native (Purescript { nativePretty })) = text nativePretty



data UnificationError :: forall k. k -> Prim.Type
data UnificationError m =
    NotInScope Var
  | Err String
  | InvalidApp Term Term
  | UnificationError Term Term 

derive instance Generic (UnificationError m) _

instance Show (UnificationError m) where
  show = genericShow

instance Pretty (UnificationError m) where
  pretty (NotInScope v) = text "Not in scope:" <+> pretty v
  pretty (Err err) = text "Error:" <+> text err
  pretty (InvalidApp a b) = text "Invalid app:" <+> pretty a <+> pretty b
  pretty (UnificationError a b) = text "Unification error:" <+> pretty a <+> text "=?=" <+> pretty b

instance Eq (UnificationError m) where
  eq = genericEq

instance ArrowObject (TT a) where
  arrowObject = Arrow 

instance Enumerable Ident where
  fromInt i = TypeVar ("t" <> show i)

instance Enumerable Var where
  fromInt = Ident <<< fromInt

instance NotInScopeError Var (UnificationError m) where 
  notInScopeError = NotInScope

instance InfiniteTypeError Var Term (UnificationError m) where
  infiniteTypeError v t = Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v

instance UnificationError Term (UnificationError m) where 
  unificationError = UnificationError 


instance
  ( MonadThrow (UnificationError n) m
  , Fresh Var m
  , Skolemize Mu Var TT
  , MonadState (TypingContext Var Mu Var TT) m
  ) => Unify Var Term m where
  unify v@(Ident i) t =
    case project t of
      Var (Ident j) | i == j -> pure unit
      _ -> substitute v t
  unify v@(Skolemized _ _ i) t =
    case project t of
      Var (Skolemized _ _ j) | i == j -> pure unit
      Var (Skolemized _ _ _) -> throwError $ unificationError (var v) t
      -- TODO is substitution always safe?                             
      _ -> substitute v t
--      _ -> throwError $ unificationError (var v) t
  unify v@(Scoped _ _) t =
    case project t of
      Var x@(Scoped _ _) | v == x -> pure unit
      -- TODO is substitution always safe?
      _ -> substitute v t


instance
  ( MonadThrow (UnificationError n) m
  , Fresh Var m
  , Skolemize Mu Var TT
  , MonadState (TypingContext Var Mu Var TT) m
  ) => Unify (TT Term) (TT Term) m where
  unify Arrow Arrow = pure unit
  -- TODO cumulativity ~ universe hierarchy
  -- * -> * must be in a higher universe than *
  -- ?? arrow has a dependent type (Star n -> Star m -> Star (max(n,m)+1)
  -- !! constraints must prevent Type in Type
  -- alternatively - who cares? maybe it's fine
  unify (Star _) (Star _) = pure unit
  unify (TypeAnnotation a ak) (TypeAnnotation b bk) = unify ak bk  *> unify a b
  unify (TypeAnnotation a _) b = unify a (cat b)
  unify a (TypeAnnotation b _) = unify (cat a) b
  unify a@(Native (Purescript na)) b@(Native (Purescript nb)) = do
    unify na.nativeType nb.nativeType
    when (na.nativePretty /= nb.nativePretty) do
       throwError $ unificationError (cat a) (cat b)
  unify a b = throwError $ unificationError (cat a) (cat b)

 

instance
  ( Monad m
  , Unify Term Term m
  , MonadState (TypingContext Var Mu Var TT) m
  , MonadThrow (UnificationError n) m
  ) => Inference Var TT Term m where
  inference Arrow = pure $ (arrow (cat (Star 1)) (arrow (cat (Star 1)) (cat (Star 1))) :< Cat Arrow)
  inference (Star i) = pure $ (cat (Star (i+1)) :< Cat (Star i))
  inference (LetRec bs a) = do
     let bx :: List _
         bx = Map.toUnfoldable bs
     flip traverse_ bx $ \(v /\ _) -> do
        t <- fresh
        assume v t
     traverse_ (\(v /\ t) -> do
        t' <- t
        assume v (head t')) bx
     a
  inference (TypeAnnotation v t) = do
    (vt :: Cofree (LambdaF Var TT) Term) <- v
    unify (head vt :: Term) t
    vt' <- rewrite (head vt)
    pure (vt' :< tail vt)
  inference (TypeLit t) = infer t 
  inference (Native (Purescript n)) = pure $ n.nativeType :< Cat (Native (Purescript n))

instance
  ( Monad m
  , Unify Term Term m
  , MonadState (TypingContext Var Mu Var TT) m
  , MonadThrow (UnificationError n) m
  ) => Composition Mu Var TT m where
  composition a b =
    case project a /\ project b of
      _ /\ Cat (TypeLit t) -> do
        at <- infer a
        arrArg /\ _ <- unifyWithArrow (head at)
        unify arrArg t
        rewrite a
      Cat (Native (Purescript na)) /\ Cat (Native (Purescript nb)) -> do
        nativeType <- head <$> infer (app a b)
        pure $ cat (Native (Purescript { nativeType
                                       , nativePretty: "(" <> na.nativePretty <> " " <> nb.nativePretty <> ")"
                                       , nativeTerm: na.nativeTerm nb.nativeTerm
                                       }))
      _ -> pure $ app a b 

instance
  ( Monad m
  , Unify Term Term m
  , MonadState (TypingContext Var Mu Var TT) m
  , MonadThrow (UnificationError n) m
  ) => Reduction Mu Var TT m where
  reduction =
    case _ of
      LetRec bi bo -> do
         -- TODO desugar recursive block to a linear sequence of lets using fix
         let inline :: Var -> Term -> Term -> Term
             inline v r = replaceFree (\w -> if w == v then Just r else Nothing)
         pure $ foldr (uncurry inline) bo (recSeq bi)
      c -> pure $ cat c

