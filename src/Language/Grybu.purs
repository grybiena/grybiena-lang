module Language.Grybu where

import Prelude

import Control.Alt ((<|>))
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Lazy (defer)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.State (class MonadState)
import Data.Array (replicate, (..))
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (fromCharArray)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, Lambda, LambdaF(..), absMany, app, cat, prettyVar, var)
import Language.Lambda.Inference (class ArrowObject, class Inference, arrow)
import Language.Lambda.Unification (class Enumerable, class Fresh, class InfiniteTypeError, class NotInScopeError, class Unification, class UnificationError, TypingContext, unificationError, unify)
import Language.Parser.Common (buildPostfixParser, identifier, integer, number, parens, reserved, reservedOp)
import Machine.Krivine (class Evaluate)
import Matryoshka.Class.Recursive (project)
import Parsing (ParserT)
import Parsing.Combinators (choice, many1Till, try)
import Parsing.Expr (buildExprParser)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (pretty, prettyPrint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Term m = Lambda Var (TT m)


data TT m a =
    Arrow 
  | Star Int
  | TypeAnnotation a (Term m)
  | Bottom String

  | TypeInt
  | TypeNumber
  | TypeEffect

  | Native (Native m)

derive instance Generic (TT m a) _

instance Show a => Show (TT m a) where
  show (TypeAnnotation a t) = "TypeAnnotation " <> show a <> " " <> show t
  show e = genericShow e


instance Functor (TT m) where
  map _ Arrow = Arrow
  map _ (Star i) = Star i
  map f (TypeAnnotation a t) = TypeAnnotation (f a) t
  map _ (Bottom e) = Bottom e
  map _ TypeInt = TypeInt
  map _ TypeNumber = TypeNumber
  map _ TypeEffect = TypeEffect
  map _ (Native n) = Native n


instance Eq a => Eq (TT m a) where
  eq = genericEq

instance Eq1 (TT m) where
  eq1 = genericEq

instance Foldable (TT m) where
  foldr _ b _ = b
  foldl _ b _ = b
  foldMap _ _ = mempty

data Var =
    TypeVar String
  | TermVar String

derive instance Generic Var _
instance Show Var where
  show = genericShow
instance Ord Var where
  compare = genericCompare
instance Eq Var where
  eq = genericEq

instance PrettyVar Var where
  prettyVar (TypeVar v) = text v
  prettyVar (TermVar v) = text v

instance PrettyLambda Var (TT m) where
  prettyAbs (TermVar i) a = (text "\\" <> prettyVar i) <+> text "->" <+> pretty a
  prettyAbs (TypeVar i) a = (text "forall" <> prettyVar i) <+> text "." <+> pretty a
  prettyApp (In (App (In (Cat Arrow)) a)) b = text "(" <> pretty a <+> text "->" <+> pretty b <> text ")"
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat Arrow = text "->"
  prettyCat (Star i) = text (fromCharArray $ replicate i '*')
  prettyCat (TypeAnnotation v t) = text "(" <> pretty v <+> text "::" <+> pretty t <> text ")"
  prettyCat (Bottom e) = text "Bottom" <+> text e
  prettyCat TypeInt = text "Int"
  prettyCat TypeNumber = text "Number"
  prettyCat TypeEffect = text "Effect" 
  prettyCat (Native (Purescript { nativeType })) = text "(_ :: " <> pretty nativeType <> text ")"


parseValue :: forall m n. Monad m => ParserT String m (Term n)
parseValue = buildExprParser [] (buildPostfixParser [parseApp, parseTypeAnnotation] parseValueAtom) 

parseValueAtom :: forall m n. Monad m => ParserT String m (Term n)
parseValueAtom = defer $ \_ -> parseAbs <|> ((var <<< TermVar) <$> identifier) <|> parseNumeric <|> parseNative "intPlus" intPlus <|> parseNative "numPlus" numPlus <|> (parens parseValue)

parseNumeric :: forall m n. Monad m => ParserT String m (Term n)
parseNumeric = (try parseNumber) <|> parseInt

parseInt :: forall m n. Monad m => ParserT String m (Term n)
parseInt = cat <<< Native <<< native <$> integer
 
parseNative :: forall m n. Monad m => String -> Native n -> ParserT String m (Term n)
parseNative name n = reserved name *> pure (cat (Native n))
 
parseNumber :: forall m n. Monad m => ParserT String m (Term n)
parseNumber = cat <<< Native <<< num <$> number

parseTypeAnnotation :: forall m n. Monad m => (Term n) -> ParserT String m (Term n)
parseTypeAnnotation v = do
  reservedOp "::"
  t <- parseType
  pure $ cat $ TypeAnnotation v t
 
parseAbs :: forall m n. Monad m => ParserT String m (Term n)
parseAbs = absMany <$> parsePats <*> parseValue
  where
    parsePats = reservedOp "\\" *> many1Till (TermVar <$> identifier) (reservedOp "->")

parseApp :: forall m n. Monad m => (Term n) -> ParserT String m (Term n)
parseApp v = app v <$> parseValueAtom

parseType :: forall m n. Monad m => ParserT String m (Term n)
parseType = buildPostfixParser [parseTypeArrow, parseTypeApp, parseTypeAnnotation] parseTypeAtom 

parseTypeAtom :: forall m n. Monad m => ParserT String m (Term n)
parseTypeAtom = defer $ \_ -> parseTypeAbs <|> ((var <<< TypeVar) <$> identifier) <|> parseStar <|> parseTypeInt <|> parseTypeNumber <|> (parens parseType)

parseTypeInt :: forall m n . Monad m => ParserT String m (Term n)
parseTypeInt = reserved "Int" *> pure (cat TypeInt)
 
parseTypeNumber :: forall m n . Monad m => ParserT String m (Term n)
parseTypeNumber = reserved "Number" *> pure (cat TypeNumber)
 

parseTypeArrow :: forall m n. Monad m => (Term n) -> ParserT String m (Term n)
parseTypeArrow a = do
  reservedOp "->"
  b <- parseType
  pure (app (app (cat Arrow) a) b)

parseStar :: forall m n . Monad m => ParserT String m (Term n)
parseStar = choice (star <$> (1 .. 4))
  where
    star i = do
      reservedOp (fromCharArray (replicate i '*'))
      pure $ cat (Star i)

parseTypeAbs :: forall m n. Monad m => ParserT String m (Term n)
parseTypeAbs = absMany <$> parsePats <*> parseType
  where
    parsePats = reservedOp "forall" *> many1Till (TypeVar <$> identifier) (reservedOp ".")

parseTypeApp :: forall m n. Monad m => (Term n) -> ParserT String m (Term n)
parseTypeApp v = app v <$> parseTypeAtom

data UnificationError m =
    NotInScope Var
  | Err String
  | InvalidApp (Term m) (Term m)
  | UnificationError (Term m) (Term m) 

derive instance Generic (UnificationError m) _
instance Show (UnificationError m) where
  show = genericShow
instance Eq (UnificationError m) where
  eq = genericEq

instance ArrowObject ((TT m) a) where
  arrowObject = Arrow

instance Enumerable Var where
  fromInt i = TypeVar ("t" <> show i)

instance NotInScopeError Var (UnificationError m) where 
  notInScopeError = NotInScope

instance InfiniteTypeError Var (Term m) (UnificationError m) where
  infiniteTypeError v t = Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v

instance UnificationError (Term m) (UnificationError m) where 
  unificationError = UnificationError 


instance
  ( MonadThrow (UnificationError n) m
  , Fresh Var m
  , MonadState (TypingContext Var Mu Var (TT n)) m
  ) => Unification (TT n (Term n)) m where
  unify Arrow Arrow = pure Arrow
  -- TODO concerned that our hierarchy of type universes may permit paradox
  -- should the type of the arrow be the max of the types of the domain/codomain i.e. (* -> * :: **)
  -- currently it is always * which is simple but probably wrong for some definition of wrong 
  -- TODO read more about Girard's paradox and implementations of cumulativity constraints
  unify (Star i) (Star j) = pure $ Star (max i j)
  unify (TypeAnnotation a ak) (TypeAnnotation b bk) = flip TypeAnnotation <$> unify ak bk  <*> unify a b
  unify (TypeAnnotation a k) b = flip TypeAnnotation k <$> unify a (cat b)
  unify a (TypeAnnotation b k) = flip TypeAnnotation k <$> unify (cat a) b
  unify TypeInt TypeInt = pure TypeInt
  unify TypeNumber TypeNumber = pure TypeNumber
  unify a b = throwError $ unificationError (cat a) (cat b)


instance
  ( Monad m
  , Unification (Term n) m
  ) => Inference Var (TT n) (Term n) m where
  inference Arrow = pure $ (arrow (cat (Star 1)) (arrow (cat (Star 1)) (cat (Star 1))) :< Cat Arrow)
  inference (Star i) = pure $ (cat (Star (i+1)) :< Cat (Star i))
  inference (TypeAnnotation v t) = do
    (t' :: Cofree (LambdaF Var (TT n)) (Term n)) <- v
    _ <- unify (t :: Term n) (head t' :: Term n)
    pure (t :< tail t')
  inference (Bottom e) = pure (cat (Bottom e) :< Cat (Bottom e))
  inference TypeInt = pure $ (cat (Star 1) :< Cat TypeInt)
  inference TypeNumber = pure $ cat (Star 1) :< Cat TypeNumber
  inference TypeEffect = pure $ arrow (cat (Star 1)) (cat (Star 1)) :< Cat TypeEffect
  inference (Native (Purescript n)) = pure $ n.nativeType :< Cat (Native (Purescript n))

instance Applicative m => Evaluate Mu Var (TT m) m where
  thunk (Native n) = pure $ Native n
  thunk e = pure $ Bottom $ "Machine terminated on a non-thunk object: " <> show (const unit <$> e)

  functor (Native (Purescript { nativeTerm, nativeType })) arg =
    case project nativeType of
      App (In (App (In (Cat Arrow)) (In (Cat argTy)))) ret -> 
        case unwrap argTy arg of
          Just i ->
            pure $ cat $ Native $ Purescript { nativeTerm: nativeTerm  i
                                       , nativeType: ret
                                       }
          Nothing -> pure $ cat $ Bottom $ "Cannot apply `_ :: " <> prettyPrint nativeType 
                                      <> "` to " <> show arg
      _ -> pure $ cat $ Bottom $ "Cannot apply `_ :: " <> prettyPrint nativeType
  functor e _ = pure $ cat $ Bottom $ "Machine applied non-functor object: " <> show (const unit <$> e)


newtype Native :: (Type -> Type) -> Type
newtype Native m = Purescript { nativeType :: Term m, nativeTerm :: forall a. a }



instance Eq (Native m) where
  eq (Purescript a) (Purescript b) = a.nativeType == b.nativeType && (a.nativeTerm :: String) == b.nativeTerm

instance Show (Native m) where
  show (Purescript { nativeType }) = "(_ :: " <> prettyPrint nativeType <> ")"

unwrap :: forall x m. (TT m) x -> (TT m) Void -> Maybe (forall a . a) 
unwrap _ (Native (Purescript { nativeTerm })) = Just nativeTerm
unwrap _ _ = Nothing

intPlus :: forall m . Native m
intPlus = native (\(a :: Int) (b :: Int) -> a + b)

numPlus :: forall m. Native m
numPlus = native (\(a :: Number) (b :: Number) -> a + b)

int :: forall m . Int -> Native m
int i = native i

num :: forall m . Number -> Native m
num i = native i

native :: forall m t . Reifies t m => t -> Native m
native term = Purescript
  { nativeType: reify (Proxy :: Proxy t)
  , nativeTerm: unsafeCoerce term
  }

pureLogInt :: forall m. Reifies m m => MonadEffect m => Native m
pureLogInt = native prim
  where
    prim :: Int -> m Int
    prim a = liftEffect (log (show a)) *> pure 0


pureEffectInt :: forall m. Reifies m m => Applicative m => Native m
pureEffectInt = native prim
  where
    prim :: Int -> m Int
    prim = pure 


class Reifies :: forall k. k -> (Type -> Type) -> Constraint
class Reifies s m where
  reify :: Proxy s -> (Term m)

instance Reifies (->) m where
  reify _ = cat Arrow
else
instance Reifies Int m where
  reify _ = cat TypeInt
else
instance Reifies Number m where
  reify _ = cat TypeNumber
else
instance (Reifies a m, Reifies b m) => Reifies (a b) m where
  reify _ = app (reify (Proxy :: Proxy a)) (reify (Proxy :: Proxy b))
else
instance Reifies m m where
  reify _ = cat TypeEffect

