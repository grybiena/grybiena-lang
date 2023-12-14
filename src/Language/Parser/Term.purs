module Language.Parser.Term where


import Prelude

import Control.Alt ((<|>))
import Control.Comonad.Cofree (head, (:<))
import Control.Lazy (defer)
import Control.Monad.Cont (lift)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable, intersperse, replicate)
import Data.Array as Array
import Data.CodePoint.Unicode (isUpper)
import Data.Foldable (foldl)
import Data.Functor.Mu (Mu)
import Data.Homogeneous (class ToHomogeneousRow)
import Data.Homogeneous.Record (fromHomogeneous, homogeneous)
import Data.List (List(..), length, (..), (:))
import Data.List as List
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NonEmptyList
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.String (codePointFromChar)
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.Tuple.Nested ((/\))
import Debug (traceM)
import Effect (Effect)
import Language.Kernel.Data (Data(..))
import Language.Kernel.Prim (primNatives)
import Language.Lambda.Calculus (LambdaF(..), absMany, app, appMany, cat, var)
import Language.Lambda.Inference (appRule, arrMany, closeTerm, flat, infer, (:->:))
import Language.Lambda.Module (Module(..))
import Language.Lambda.Unification (class Fresh, class InfiniteTypeError, class NotInScopeError, TypingContext, fresh, renameFresh, rewrite)
import Language.Lambda.Unification.Error (class ThrowUnificationError)
import Language.Native (Native(..), native)
import Language.Native.Module (Listing, NativeModule, moduleListing)
import Language.Native.Reify (nativeTerm, reify)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Basis (class StringParserT, class BasisParser)
import Language.Parser.Common (buildPostfixParser, languageDef)
import Language.Parser.Indent (IndentParserT, Positioned, block1, indented, runIndentT, withPos, withPos')
import Language.Term (CaseAlternative(..), DataType(..), DataTypeDecl(..), DataValueDecl(..), Ident(..), Scope(..), TT(..), Term, TypedTerm, Var(..), freshTermVar)
import Parsing (fail, runParserT)
import Parsing.Combinators (choice, many, many1, many1Till, try)
import Parsing.Expr (buildExprParser)
import Parsing.String (char, eof)
import Parsing.Token (GenTokenParser, makeTokenParser)
import Prettier.Printer (beside, text, (<+>))
import Pretty.Printer (pretty, prettyPrint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

instance
  ( Fresh Int m
  , MonadState (TypingContext Var Mu Var TT) m
  , ThrowUnificationError Term m
  , InfiniteTypeError Var Term m
  , NotInScopeError Var m
  , MonadRec m
  ) => BasisParser Parser m Mu Var TT where
  parseBasis = do
    t <- (parser (homogeneous {})).parseType
    Parser eof
    pure t

instance MonadRec m => StringParserT Parser m where
  runStringParserT s (Parser p) = runIndentT $ runParserT s p

newtype Parser m a = Parser (IndentParserT m a)
derive newtype instance Functor (Parser m)
derive newtype instance Apply (Parser m)
derive newtype instance Applicative (Parser m)
derive newtype instance Bind (Parser m)
derive newtype instance Monad m => Monad (Parser m)

type TermParser m =
  { parseValue:: Parser m Term
  , parseType :: Parser m Term
  , parseModule :: Parser m (Module Var Term)
  }

data Decl =
    TypeDecl Var Term
  | ValueDecl Var Term
  | DataDecl DataTypeDecl (List DataValueDecl)


dataConstructors :: forall m.
                    MonadRec m
                 => MonadState (TypingContext Var Mu Var TT) m
                 => ThrowUnificationError Term m
                 => InfiniteTypeError Var Term m
                 => NotInScopeError Var m
                 => DataTypeDecl -> List DataValueDecl -> m (List Decl)
dataConstructors t@(DataTypeDecl tc _) cs = pure $ ty:(co <$> cs) 
  where
    dt = (DataType t cs)
    ty = ValueDecl (Ident $ TypeVar tc) (cat (TypeCon tc dt)) 
    co (DataValueDecl c _) = ValueDecl (Ident $ TermVar c) (cat (DataCon c dt)) 

instance Show Decl where
  show (TypeDecl v t) = prettyPrint v <> " :: " <> prettyPrint t
  show (ValueDecl v t) = prettyPrint v <> " = " <> prettyPrint t
  show (DataDecl (DataTypeDecl t vs) cs) =
    let prettyCon (DataValueDecl s v) = foldl beside (text s) (pretty <$> v)
     in prettyPrint $ text "data" <+> foldl beside (text t) (pretty <$> vs)
                                  <+> text "="
                                  <+> foldl beside (text "") (intersperse (text "|") (fromFoldable $ prettyCon <$> cs))

parser :: forall names row m.
          Fresh Int m
       => MonadRec m
       => ThrowUnificationError Term m
       => InfiniteTypeError Var Term m
       => NotInScopeError Var m
       => MonadState (TypingContext Var Mu Var TT) m
       => ToHomogeneousRow names (IndentParserT m (Native Term)) row
       => NativeModule names (IndentParserT m (Native Term))
       -> TermParser m
parser mod = {
    parseValue: Parser parseValue
  , parseType: Parser parseType
  , parseModule: Parser ((try parseModuleB) <|> parseModuleI)
  }
  where
    kernel :: Listing (IndentParserT m (Native Term))
    kernel = moduleListing mod

    tokenParser :: GenTokenParser String (Positioned m)
    tokenParser = makeTokenParser (languageDef (fromFoldable (fst <$> kernel)))

    integer :: IndentParserT m Int
    integer = tokenParser.integer 
    
    number :: IndentParserT m Number
    number = tokenParser.float
    
    reservedOp :: String -> IndentParserT m Unit
    reservedOp = tokenParser.reservedOp
     
    reserved :: String -> IndentParserT m Unit
    reserved = tokenParser.reserved

    identifier :: IndentParserT m String
    identifier = tokenParser.identifier
        
    parens :: forall a. IndentParserT m a -> IndentParserT m a
    parens = tokenParser.parens
     
    parseModuleX :: (forall a. IndentParserT m a -> IndentParserT m (NonEmptyList a))
                 -> IndentParserT m (Module Var Term)
    parseModuleX f = do
      ls <- List.fromFoldable <$> f (try parseDataDecl <|> try parseTypeDecl <|> parseValueDecl)
      ds <- tailRecM annotateVals (Nil /\ ls)
      pure $ Module (Map.fromFoldable ds)
      where
        annotateVals (d /\ Nil) = pure $ Done d
        annotateVals (d /\ ((ValueDecl v b):r)) = pure $ Loop (((v /\ b):d) /\ r)
        annotateVals (d /\ ((TypeDecl vt t):(ValueDecl vv v):r)) | vt == vv =
           pure $ Loop (((vv /\ (cat $ TypeAnnotation v t)):d) /\ r)
        annotateVals (_ /\ (TypeDecl vt _):r) = fail $ prettyPrint vt <> " type declaration not followed by value declaration. " <> show r
        annotateVals (d /\ ((DataDecl dtc z):r)) = do
           dcs <- lift $ lift $ dataConstructors dtc z
           pure $ Loop (d /\ (dcs <> r))
        parseTypeDecl = do
           v <- parseTermVar 
           reservedOp "::"
           b <- parseType
           pure (TypeDecl v b)
        parseValueDecl = do
           v <- parseTermVar 
           reservedOp "="
           b <- parseValue
           pure (ValueDecl v b)
        parseDataDecl = withPos' (reserved "data") do
           dtc@(DataTypeDecl c _) <- parseDataTypeDecl
           reservedOp "="
           fcon <- withPos parseDataValueDecl
           dcons <- many (indented *> (reservedOp "|") *> withPos parseDataValueDecl)
           pure (DataDecl dtc (fcon:dcons))
        parseDataTypeDecl = do
           con <- parseDataConstructor'
           tvs <- many parseTypeVar
           pure (DataTypeDecl con tvs)
        parseDataValueDecl = do
           dcon <- parseDataConstructor'
           tvs <- many (indented *> ((try (var <$> parseTypeVar)) <|> (try (var <$> parseTypeConstructor)) <|> parseTypeAtom))
           pure $ DataValueDecl dcon tvs


    parseBinder :: Monad m => IndentParserT m Term
    parseBinder = do
      i <- identifier 
      if Just false == ((isUpper <<< codePointFromChar) <$> (Array.head $ toCharArray i))
        then pure $ cat $ Binder i
        else fail "Binders must not start with an upper case char"



    parseTermVar :: Monad m => IndentParserT m Var
    parseTermVar = do
      i <- identifier 
      if Just false == ((isUpper <<< codePointFromChar) <$> (Array.head $ toCharArray i))
        then pure $ Ident $ TermVar i
        else fail "Term variables must not start with an upper case char"

    parseDataConstructor :: forall abs . Monad m => IndentParserT m (Mu (LambdaF abs Var TT))
    parseDataConstructor = (cat <<< Data <<< flip DataConstructor Nothing) <$> parseDataConstructor'

    parsePatternConstructor :: forall abs . Monad m => IndentParserT m (Mu (LambdaF abs Var TT))
    parsePatternConstructor = (cat <<< Pattern) <$> parseDataConstructor'


    parseDataConstructor' :: Monad m => IndentParserT m String
    parseDataConstructor' = do
      i <- identifier 
      if Just true == ((isUpper <<< codePointFromChar) <$> (Array.head $ toCharArray i))
        then pure i
        else fail "Data constructors must start with an upper case char"



    parseTypeVar :: Monad m => IndentParserT m Var
    parseTypeVar = do
      i <- identifier 
      if Just false == ((isUpper <<< codePointFromChar) <$> (Array.head $ toCharArray i))
        then pure $ Ident $ TypeVar i
        else fail "Type variables must not start with an upper case char"

    parseTypeConstructor :: Monad m => IndentParserT m Var
    parseTypeConstructor = do
      i <- identifier 
      if Just true == ((isUpper <<< codePointFromChar) <$> (Array.head $ toCharArray i))
        then pure $ Ident $ TypeVar i
        else fail "Type constructors must start with an upper case char"



    parseModuleB :: Monad m => IndentParserT m (Module Var Term)
    parseModuleB = parseModuleX ((map NonEmptyList.fromFoldable <<< tokenParser.braces <<< tokenParser.semiSep1)
                                >=> maybe (fail "Empty module.") pure)

    parseModuleI :: Monad m => IndentParserT m (Module Var Term)
    parseModuleI = parseModuleX block1

    parseLet :: IndentParserT m Term
    parseLet = (try parseLetB) <|> parseLetI 
      where
        parseLetI :: IndentParserT m Term
        parseLetI = do
          b <- withPos' (reserved "let") do
             indented
             parseModuleI
          reserved "in"
          body <- parseValue
          pure $ cat $ Let b body
    
        parseLetB :: IndentParserT m Term
        parseLetB = do
          reserved "let"
          b <- parseModuleB
          reserved "in"
          body <- parseValue
          pure $ cat $ Let b body

    parseValue :: Monad m => IndentParserT m Term
    parseValue = indented *> (buildExprParser [] (buildPostfixParser [parseApp, parseTypeAnnotation] parseValueAtom)) 
    
    parseValueAtom :: IndentParserT m Term
    parseValueAtom = defer $ \_ -> indented *> (parseCaseExpr <|> parseAbs <|> parseNatives <|> (try (var <$> parseTermVar) <|> (var <<< Ident <<< TermVar <$> parseDataConstructor')) <|> parseNumeric <|> parseTypeLit <|> parseLet <|> parseIfElse <|> (parens parseValue))
 
    parsePattern :: Monad m => IndentParserT m Term 
    parsePattern = (buildExprParser [] (buildPostfixParser [parsePatternApp, parseTypeAnnotation] parsePatternAtom)) 
 
    parsePatternAtom :: IndentParserT m Term 
    parsePatternAtom = defer $ \_ -> ((try parseBinder <|> parsePatternConstructor) <|> parseNumeric <|> (parens parsePattern))
 
    
    parseTypeLit :: IndentParserT m Term
    parseTypeLit = char '@' *> ((cat <<< TypeLit) <$> parseTypeAtom)
    
    parseNumeric :: forall abs. IndentParserT m (Mu (LambdaF abs Var TT))
    parseNumeric = (try parseNumber) <|> parseInt
    
    parseInt :: forall abs. IndentParserT m (Mu (LambdaF abs Var TT))
    parseInt = cat <<< Native <<< (\i -> nativeTerm (show i) i) <$> integer
     
    parseNatives :: IndentParserT m Term
    parseNatives = choice $ map (uncurry parseNative) kernel
     
    parseNative ::  String -> IndentParserT m (Native Term) -> IndentParserT m Term
    parseNative name native = reserved name *> ((cat <<< Native) <$> native)
     
    parseNumber :: forall abs. IndentParserT m (Mu (LambdaF abs Var TT))
    parseNumber = cat <<< Native <<< (\i -> nativeTerm (show i) i) <$> number 

    parseCaseExpr :: Monad m => IndentParserT m Term
    parseCaseExpr = do
      withPos' (reserved "case") do
        exps <- many1 parseValueAtom
        reserved "of"
        alts <- block1 parseCaseAlternative
        pure $ cat (Case exps alts) 

    parseCaseAlternative :: Monad m => IndentParserT m (CaseAlternative Term)
    parseCaseAlternative = do
       patterns <- many1Till parsePatternAtom (reservedOp "=>")
       body <- parseValue
       pure $ CaseAlternative { patterns, guard: Nothing, body }


    
    parseIfElse :: IndentParserT m Term
    parseIfElse = do
      reserved "if"
      x <- parseValue
      reserved "then"
      a <- parseValue
      reserved "else"
      b <- parseValue
      i <- native <$> (fromHomogeneous (unsafeModule (Proxy :: Proxy Parser) primNatives))."ifElse"
      pure $ app (app (app i x) a) b

    
    parseTypeAnnotation ::forall abs. (Mu (LambdaF abs Var TT)) -> IndentParserT m (Mu (LambdaF abs Var TT))
    parseTypeAnnotation v = do
      reservedOp "::"
      t <- parseType
      pure $ cat $ TypeAnnotation v t
 
    parseAbs :: IndentParserT m Term
    parseAbs = absMany <$> parsePats <*> parseValue
      where
        parsePats = reservedOp "\\" *> many1Till (Ident <<< TermVar <$> identifier) (reservedOp "->")
    
    parseApp :: Term -> IndentParserT m Term
    parseApp v = app v <$> parseValueAtom
    
    parsePatternApp :: Term -> IndentParserT m Term
    parsePatternApp v = app v <$> parsePatternAtom
 
    parseType :: Monad m => IndentParserT m Term
    parseType = indented *> (buildPostfixParser [parseTypeArrow, parseTypeApp, parseTypeAnnotation] parseTypeAtom) 
    
    parseTypeAtom :: IndentParserT m Term
    parseTypeAtom = defer $ \_ -> indented *> (parseTypeAbs <|> (try (var <$> parseTypeVar) <|> (var <$> parseTypeConstructor)) <|> parseStar <|> parseTypeInt <|> parseTypeNumber <|> parseTypeEffect <|> (parens parseType))
    
    parseTypeInt ::  IndentParserT m Term
    parseTypeInt = reserved "Int" *> pure (reify (Proxy :: Proxy Int))
     
    parseTypeNumber :: IndentParserT m Term
    parseTypeNumber = reserved "Number" *> pure (reify (Proxy :: Proxy Number))
      
    parseTypeEffect ::  IndentParserT m Term
    parseTypeEffect = reserved "Effect" *> pure (reify (Proxy :: Proxy Effect))
    

    
    parseTypeArrow :: Term -> IndentParserT m Term
    parseTypeArrow a = do
      reservedOp "->"
      b <- parseType
      pure (app (app (cat Arrow) a) b)
    
    parseStar ::  IndentParserT m Term
    parseStar = choice (star <$> (1 .. 4))
      where
        star i = do
          reservedOp (fromCharArray (replicate i '*'))
          pure $ cat (Star i)
    
    parseTypeAbs :: IndentParserT m Term
    parseTypeAbs = absMany <$> parsePats <*> parseType
      where
        parsePats = reservedOp "forall" *> many1Till scopedVar (reservedOp ".")
        scopedVar = do
          i <- identifier
          s <- lift $ lift fresh
          pure $ Scoped (TypeVar i) (Scope s)
    
    parseTypeApp :: Term -> IndentParserT m Term
    parseTypeApp v = app v <$> parseTypeAtom
    

