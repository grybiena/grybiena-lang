module Language.Grybu where

import Prelude

import Control.Alt ((<|>))
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Lazy (defer)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Rec.Class (class MonadRec, Step(..))
import Control.Monad.State (class MonadState)
import Data.Array (replicate, (..))
import Data.Either (Either(..))
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (fromCharArray)
import Data.Tuple (fst, uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, Lambda, LambdaF(..), abs, absMany, app, cat, prettyVar, var)
import Language.Lambda.Inference (class ArrowObject, class Inference, arrow)
import Language.Lambda.Unification (class Enumerable, class Fresh, class InfiniteTypeError, class NotInScopeError, class Unification, class UnificationError, TypingContext, fresh, rewrite, runUnification, unificationError, unify)
import Language.Parser.Common (buildPostfixParser, identifier, integer, number, parens, reserved, reservedOp)
import Machine.Krivine (class Evaluate, class MachineFault)
import Matryoshka.Class.Recursive (project)
import Parsing (ParserT)
import Parsing.Combinators (choice, many1Till, try)
import Parsing.Expr (buildExprParser)
import Parsing.String (char)
import Prettier.Printer (text, (<+>))
import Pretty.Printer (class Pretty, pretty, prettyPrint)
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

  | BindEffect
  | TypeAnnotation a (Term m)
  | Native (Native m)

derive instance Generic (TT m a) _

instance Show a => Show (TT m a) where
  show (TypeAnnotation a t) = "TypeAnnotation " <> show a <> " " <> show t
  show e = genericShow e


instance Functor (TT m) where
  map _ Arrow = Arrow
  map _ (Star i) = Star i
  map _ (Bottom e) = Bottom e
  map _ TypeInt = TypeInt
  map _ TypeNumber = TypeNumber
  map _ TypeEffect = TypeEffect

  map _ BindEffect = BindEffect
  map f (TypeAnnotation a t) = TypeAnnotation (f a) t
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

instance Pretty Var where
  pretty = prettyVar

instance PrettyLambda Var (TT m) where
  prettyAbs (TermVar i) a = (text "\\" <> prettyVar i) <+> text "->" <+> pretty a
  prettyAbs (TypeVar i) a = (text "forall " <> prettyVar i) <+> text "." <+> pretty a
  prettyApp (In (App (In (Cat Arrow)) a)) b = text "(" <> pretty a <+> text "->" <+> pretty b <> text ")"
  prettyApp f a = text "(" <+> pretty f <+> pretty a <+> text ")"
  prettyCat Arrow = text "->"
  prettyCat (Star i) = text (fromCharArray $ replicate i '*')
  prettyCat (Bottom e) = text "Bottom" <+> text e
  prettyCat TypeInt = text "Int"
  prettyCat TypeNumber = text "Number"
  prettyCat TypeEffect = text "Effect" 
  prettyCat BindEffect = text "bindEffect"

  prettyCat (TypeAnnotation v t) = text "(" <> pretty v <+> text "::" <+> pretty t <> text ")"
  prettyCat (Native (Purescript { nativeType })) = text "(_ :: " <> pretty nativeType <> text ")"


parseValue :: forall m n. Monad m => Monad n => ParserT String m (Term n)
parseValue = buildExprParser [] (buildPostfixParser [parseApp, parseTypeAnnotation] parseValueAtom) 

parseValueAtom :: forall m n. Monad m => Monad n => ParserT String m (Term n)
parseValueAtom = defer $ \_ -> parseAbs <|> ((var <<< TermVar) <$> identifier) <|> parseNumeric <|> parseNative "intPlus" intPlus <|> parseNative "numPlus" numPlus <|> parsePureEffect <|> parseBindEffect <|> parseTypeLit <|> (parens parseValue)

parseTypeLit :: forall m n. Monad m => ParserT String m (Term n)
parseTypeLit = char '@' *> parseTypeAtom 

parseNumeric :: forall m n. Monad m => ParserT String m (Term n)
parseNumeric = (try parseNumber) <|> parseInt

parseInt :: forall m n. Monad m => ParserT String m (Term n)
parseInt = cat <<< Native <<< native <$> integer
 
parsePureEffect :: forall m n. Monad m => Monad n => ParserT String m (Term n)
parsePureEffect = reserved "pureEffect" *> pure (cat $ Native pureE)

parseBindEffect :: forall m n. Monad m => Bind n => ParserT String m (Term n)
parseBindEffect = reserved "bindEffect" *> pure (cat BindEffect) 
 
parseNatives :: forall m n. Monad m => Array (String /\ Native n) -> ParserT String m (Term n)
parseNatives = choice <<< map (uncurry parseNative)
 
parseNative :: forall m n. Monad m => String -> Native n -> ParserT String m (Term n)
parseNative name n = reserved name *> pure (cat (Native n))
 
parseNumber :: forall m n. Monad m => ParserT String m (Term n)
parseNumber = cat <<< Native <<< num <$> number

parseTypeAnnotation :: forall m n. Monad m => (Term n) -> ParserT String m (Term n)
parseTypeAnnotation v = do
  reservedOp "::"
  t <- parseType
  pure $ cat $ TypeAnnotation v t
 
parseAbs :: forall m n. Monad m => Monad n => ParserT String m (Term n)
parseAbs = absMany <$> parsePats <*> parseValue
  where
    parsePats = reservedOp "\\" *> many1Till (TermVar <$> identifier) (reservedOp "->")

parseApp :: forall m n. Monad m => Monad n => (Term n) -> ParserT String m (Term n)
parseApp v = app v <$> parseValueAtom

parseType :: forall m n. Monad m => ParserT String m (Term n)
parseType = buildPostfixParser [parseTypeArrow, parseTypeApp, parseTypeAnnotation] parseTypeAtom 

parseTypeAtom :: forall m n. Monad m => ParserT String m (Term n)
parseTypeAtom = defer $ \_ -> parseTypeAbs <|> ((var <<< TypeVar) <$> identifier) <|> parseStar <|> parseTypeInt <|> parseTypeNumber <|> parseTypeEffect <|> (parens parseType)

parseTypeInt :: forall m n . Monad m => ParserT String m (Term n)
parseTypeInt = reserved "Int" *> pure (cat TypeInt)
 
parseTypeNumber :: forall m n . Monad m => ParserT String m (Term n)
parseTypeNumber = reserved "Number" *> pure (cat TypeNumber)
  
parseTypeEffect :: forall m n . Monad m => ParserT String m (Term n)
parseTypeEffect = reserved "Effect" *> pure (cat TypeEffect)


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

instance Pretty (UnificationError m) where
  pretty (NotInScope v) = text "Not in scope:" <+> pretty v
  pretty (Err err) = text "Error:" <+> text err
  pretty (InvalidApp a b) = text "Invalid app:" <+> pretty a <+> pretty b
  pretty (UnificationError a b) = text "Unification error:" <+> pretty a <+> text "=?=" <+> pretty b

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
  unify TypeEffect TypeEffect = pure TypeEffect
  unify a b = throwError $ unificationError (cat a) (cat b)

instance 
  ( MonadRec m
  , Evaluate Mu Var (TT n) m
  , MonadEffect m
  ) => MachineFault Mu Var (TT n) Map m where
  contextFault _ v = pure $ Done $ Bottom $ "Variable `" <> prettyPrint v <> "` not in scope."
  stackFault _ _ = pure $ Done $ Bottom "Stack fault"
  

instance
  ( Monad m
  , Unification (Term n) m
  , MonadState (TypingContext Var Mu Var (TT n)) m
  ) => Inference Var (TT n) (Term n) m where
  inference Arrow = pure $ (arrow (cat (Star 1)) (arrow (cat (Star 1)) (cat (Star 1))) :< Cat Arrow)
  inference (Star i) = pure $ (cat (Star (i+1)) :< Cat (Star i))
  inference (Bottom e) = pure (cat (Bottom e) :< Cat (Bottom e))
  inference TypeInt = pure $ (cat (Star 1) :< Cat TypeInt)
  inference TypeNumber = pure $ cat (Star 1) :< Cat TypeNumber
  inference TypeEffect = pure $ arrow (cat (Star 1)) (cat (Star 1)) :< Cat TypeEffect

  inference (TypeAnnotation v t) = do
    (t' :: Cofree (LambdaF Var (TT n)) (Term n)) <- v
    _ <- unify (t :: Term n) (head t' :: Term n)
    pure (t :< tail t')
  inference BindEffect = do
    va <- pure $ TypeVar "ta" -- fresh
    vb <- pure $ TypeVar "tb" -- fresh
    let a = var va
        b = var vb 
    pure $ abs va (abs vb (arrow (app (cat TypeEffect) a) (arrow (arrow a (app (cat TypeEffect) b)) (app (cat TypeEffect) b)))) :< Cat BindEffect

  inference (Native (Purescript n)) = pure $ n.nativeType :< Cat (Native (Purescript n))

instance
  ( Monad m
  ) => Evaluate Mu Var (TT n) m where
  thunk (Native n@(Purescript { nativeType, nativeTerm })) =
    case project nativeType of
      App (In (Cat TypeEffect)) ret -> do
        res <- (unsafeCoerce nativeTerm :: m (forall a. a))
        pure $ Native (Purescript { nativeType: ret, nativeTerm: res })
      _ -> pure $ Native n
  thunk TypeInt = pure TypeInt
  thunk e = pure $ Bottom $ "Machine terminated on a non-thunk object: " <> show (const unit <$> e)

  functor (Native (Purescript { nativeTerm, nativeType })) arg =
    case project nativeType of
      -- Value level lambda application
      App (In (App (In (Cat Arrow)) _)) ret -> 
        case arg of
          Native (Purescript argTerm) ->
            pure $ cat $ Native $ Purescript { nativeTerm: nativeTerm argTerm.nativeTerm , nativeType: ret }
          _ -> pure $ cat $ Bottom $ "Cannot apply `_ :: " <> prettyPrint nativeType <> "` to unwrappable " <> show arg
      -- Type level lambda application
      Abs v b -> do
         -- TODO maintain the unification context from when the program the machine is running was inferred
         -- (runUnification should be in m)
         let ret = fst $ runUnification do
                     void $ unify (var v) (cat (unsafeCoerce arg) :: Term n)
                     rewrite b
         case ret of
           Left (err :: UnificationError n) -> pure $ cat $ Bottom $ "Run-time type application error: " <> show err 
           Right rew -> pure $ cat $ Native $ Purescript { nativeTerm: unsafeCoerce nativeTerm, nativeType: rew }
      _ -> pure $ cat $ Bottom $ "Cannot apply `_ :: " <> prettyPrint nativeType
  functor e _ = pure $ cat $ Bottom $ "Machine applied non-functor object: " <> show (const unit <$> e)


newtype Native :: (Type -> Type) -> Type
newtype Native m = Purescript { nativeType :: Term m, nativeTerm :: forall a. a }



instance Eq (Native m) where
  eq (Purescript a) (Purescript b) = a.nativeType == b.nativeType && (a.nativeTerm :: String) == b.nativeTerm

instance Show (Native m) where
  show (Purescript { nativeType, nativeTerm }) = "(" <> unsafeCoerce nativeTerm <> " :: " <> prettyPrint nativeType <> ")"

unwrap :: forall m. (TT m) Void -> Maybe (forall a . a) 
unwrap (Native (Purescript { nativeTerm })) = Just nativeTerm
unwrap _ = Nothing

intPlus :: forall m . Native m
intPlus = native (\(a :: Int) (b :: Int) -> a + b)

numPlus :: forall m. Native m
numPlus = native (\(a :: Number) (b :: Number) -> a + b)

int :: forall m . Int -> Native m
int i = native i

num :: forall m. Number -> Native m
num i = native i

native :: forall m t . Reifies t m => t -> Native m
native term = Purescript
  { nativeType: reify (Proxy :: Proxy t)
  , nativeTerm: unsafeCoerce term
  }

logInt :: forall m. Reifies m m => MonadEffect m => Native m
logInt = native prim
  where
    prim :: Int -> m Int
    prim a = liftEffect (log (show a)) *> pure 0

pureE :: forall m. Applicative m => Native m
pureE = Purescript
  { -- TODO generate fresh type variables when parsing
    nativeType: abs (TypeVar "a") (arrow (var (TypeVar "a")) (app (cat TypeEffect) (var (TypeVar "a")))) 
  , nativeTerm:
      let prim :: forall a. a -> m a
          prim = pure
       in unsafeCoerce prim
  }
 
bindE :: forall m. Bind m => Native m
bindE = Purescript
  { -- TODO generate fresh type variables when parsing
    nativeType:
      let va = TypeVar "a"
          a = var va
          vb = TypeVar "b"
          b = var vb 
       in abs va (abs vb (arrow (app (cat TypeEffect) a) (arrow (arrow a (app (cat TypeEffect) b)) (app (cat TypeEffect) b))))
  , nativeTerm:
      let prim :: forall a b. m a -> (a -> m b) -> m b
          prim = (>>=)
       in unsafeCoerce prim
  }
 

natives :: forall m. Reifies m m => MonadEffect m =>  Array (String /\ Native m)
natives =
  [ "intPlus" /\ intPlus
  , "numPlus" /\ numPlus
  , "logInt" /\ logInt
  ]


-- better to use homogenous records
-- natives :: forall row m . Homogeneous row (Native m) => Record row
--
-- then combine using disjoint union (preventing overlap of names)
-- allowing modularisation of Native effects which have different constraints
--
-- then unfold into Array (String /\ Native m) and build the parser for that constrained runtime

data U (a :: Symbol)

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



