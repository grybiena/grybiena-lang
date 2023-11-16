module Language.Grybu where

import Prelude

import Control.Alt ((<|>))
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Lazy (defer)
import Control.Monad.Cont (lift)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (class MonadState)
import Data.Array (replicate, (..))
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.FoldableWithIndex (foldrWithIndex)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Homogeneous (class HomogeneousRowLabels, class ToHomogeneousRow)
import Data.Homogeneous.Record (Homogeneous, fromHomogeneous, homogeneous)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, Lambda, LambdaF(..), abs, absMany, app, cat, prettyVar, replace, var)
import Language.Lambda.Inference (class ArrowObject, class Inference, class IsStar, class Shadow, arrow, (:->:))
import Language.Lambda.Reduction (class Basis)
import Language.Lambda.Unification (class Enumerable, class Fresh, class InfiniteTypeError, class NotInScopeError, class Skolemize, class UnificationError, class Unify, Skolem, TypingContext, fresh, fromInt, substitute, unificationError, unify)
import Language.Parser.Common (buildPostfixParser, identifier, integer, number, parens, reserved, reservedOp)
import Language.Value.Native (Native(..))
import Matryoshka.Class.Recursive (project)
import Parsing (ParserT)
import Parsing.Combinators (choice, many1Till, try)
import Parsing.Expr (buildExprParser)
import Parsing.String (char)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty, prettyPrint)
import Prim.Row (class Union)
import Record (union)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Term m = Lambda Var (TT m)


data TT m a =
  -- Types
    Star Int
  | Arrow 
  | Bottom String
  | TypeInt
  | TypeNumber
  | TypeEffect

  -- Values

  | TypeAnnotation a (Term m)
  | Native (Native (Term m))

derive instance Generic (TT m a) _

instance Show a => Show (TT m a) where
  show (TypeAnnotation a t) = "TypeAnnotation " <> show a <> " " <> show t
  show e = genericShow e

instance IsStar Mu Var (TT m) where
  isStar t = case project t of
               Cat (Star _) -> true
               _ -> false

instance Functor (TT m) where
  map _ Arrow = Arrow
  map _ (Star i) = Star i
  map _ (Bottom e) = Bottom e
  map _ TypeInt = TypeInt
  map _ TypeNumber = TypeNumber
  map _ TypeEffect = TypeEffect

  map f (TypeAnnotation a t) = TypeAnnotation (f a) t
  map _ (Native n) = Native n

instance Traversable (TT m) where
  traverse _ Arrow = pure Arrow
  traverse _ (Star i) = pure (Star i)
  traverse _ (Bottom e) = pure (Bottom e)
  traverse _ TypeInt = pure TypeInt
  traverse _ TypeNumber = pure TypeNumber
  traverse _ TypeEffect = pure TypeEffect
  traverse f (TypeAnnotation a t) = flip TypeAnnotation t <$> (f a)
  traverse _ (Native n) = pure (Native n)
  sequence = traverse identity

instance Skolemize Mu Var (TT m) where
  skolemize (Scoped i s) k = replace (\x -> if x == Ident i then Just (var (Skolemized i s k)) else Nothing) 
  -- TODO error if the Var is not Scoped
  skolemize _ _ = identity

instance Eq a => Eq (TT m a) where
  eq = genericEq

instance Eq1 (TT m) where
  eq1 = genericEq

instance Foldable (TT m) where
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

instance PrettyLambda Var (TT m) where
  prettyAbs i a | isTypeVar i = text "(forall " <> prettyVar i <+> text "." <+> pretty a <> text ")"
  prettyAbs i a = text "(\\" <> prettyVar i <+> text "->" <+> pretty a <> text ")"
  prettyApp (In (App (In (Cat Arrow)) a)) b = text "(" <> pretty a <+> text "->" <+> pretty b <> text ")"
  prettyApp f a = text "(" <> pretty f <+> pretty a <> text ")"
  prettyCat Arrow = text "->"
  prettyCat (Star i) = text (fromCharArray $ replicate i '*')
  prettyCat (Bottom e) = text "Bottom" <+> text e
  prettyCat TypeInt = text "Int"
  prettyCat TypeNumber = text "Number"
  prettyCat TypeEffect = text "Effect" 

  prettyCat (TypeAnnotation v t) = text "(" <> pretty v <+> text "::" <+> pretty t <> text ")"
  prettyCat (Native (Purescript { nativeType })) = text "(_ :: " <> pretty nativeType <> text ")"


data UnificationError m =
    NotInScope Var
  | Err String
  | InvalidApp (Term m) (Term m)
  | UnificationError (Term m) (Term m) 

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

instance ArrowObject ((TT m) a) where
  arrowObject = Arrow

instance Enumerable Ident where
  fromInt i = TypeVar ("t" <> show i)

instance Enumerable Var where
  fromInt = Ident <<< fromInt

instance NotInScopeError Var (UnificationError m) where 
  notInScopeError = NotInScope

instance InfiniteTypeError Var (Term m) (UnificationError m) where
  infiniteTypeError v t = Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v

instance UnificationError (Term m) (UnificationError m) where 
  unificationError = UnificationError 


instance
  ( MonadThrow (UnificationError n) m
  , Fresh Var m
  , Skolemize Mu Var (TT n)
  , MonadState (TypingContext Var Mu Var (TT n)) m
  ) => Unify Var (Term n) m where
  unify v@(Ident i) t =
    case project t of
      Var (Ident j) | i == j -> pure unit
      _ -> substitute v t
  unify v@(Skolemized _ _ i) t =
    case project t of
      Var (Skolemized _ _ j) | i == j -> pure unit
      _ -> throwError $ unificationError (var v) t
  unify v t = throwError $ unificationError (var v) t


instance
  ( MonadThrow (UnificationError n) m
  , Fresh Var m
  , Skolemize Mu Var (TT n)
  , MonadState (TypingContext Var Mu Var (TT n)) m
  ) => Unify (TT n (Term n)) (TT n (Term n)) m where
  unify Arrow Arrow = pure unit
  -- TODO concerned that our hierarchy of type universes may permit paradox
  -- should the type of the arrow be the max of the types of the domain/codomain i.e. (* -> * :: **)
  -- currently it is always * which is simple but probably wrong for some definition of wrong 
  -- TODO read more about Girard's paradox and implementations of cumulativity constraints
  unify (Star _) (Star _) = pure unit
  unify (TypeAnnotation a ak) (TypeAnnotation b bk) = unify ak bk  *> unify a b
  unify (TypeAnnotation a _) b = unify a (cat b)
  unify a (TypeAnnotation b _) = unify (cat a) b
  unify TypeInt TypeInt = pure unit
  unify TypeNumber TypeNumber = pure unit
  unify TypeEffect TypeEffect = pure unit
  unify a b = throwError $ unificationError (cat a) (cat b)

 

instance
  ( Monad m
  , Unify (Term n) (Term n) m
  , MonadState (TypingContext Var Mu Var (TT n)) m
  , MonadThrow (UnificationError n) m
  ) => Inference Var (TT n) (Term n) m where
  inference Arrow = pure $ (arrow (cat (Star 1)) (arrow (cat (Star 1)) (cat (Star 1))) :< Cat Arrow)
  inference (Star i) = pure $ (cat (Star (i+1)) :< Cat (Star i))
  inference (Bottom e) = pure (cat (Bottom e) :< Cat (Bottom e))
  inference TypeInt = pure $ (cat (Star 1) :< Cat TypeInt)
  inference TypeNumber = pure $ cat (Star 1) :< Cat TypeNumber
  inference TypeEffect = pure $ arrow (cat (Star 1)) (cat (Star 1)) :< Cat TypeEffect

  inference (TypeAnnotation v t) = do
    (t' :: Cofree (LambdaF Var (TT n)) (Term n)) <- v
    unify (t :: Term n) (head t' :: Term n)
    pure (t :< tail t')
  inference (Native (Purescript n)) = pure $ n.nativeType :< Cat (Native (Purescript n))

instance
  ( Monad n
  , Fresh Var n
  ) => Basis (TT m) n where
  basisS = do
    a <- fresh
    b <- fresh
    c <- fresh
    pure $ Native $ Purescript
      { nativeType: ((var a :->: var b :->: var c) :->: (var a :->: var b) :->: var a :->: var c)
      , nativeTerm:
          let prim :: forall a b c. (a -> b -> c) -> (a -> b) -> a -> c 
              prim x y z = x z (y z)
           in unsafeCoerce prim
      }
  basisK = do
    a <- fresh
    b <- fresh
    pure $ Native $ Purescript
      { nativeType: (var a :->: var b :->: var a)
      , nativeTerm:
          let prim :: forall a b. a -> b -> a
              prim = const
           in unsafeCoerce prim
      }
  basisI = do
    a <- fresh
    pure $ Native $ Purescript
      { nativeType: (var a :->: var a)
      , nativeTerm:
          let prim :: forall a. a -> a
              prim = identity
           in unsafeCoerce prim
      }


