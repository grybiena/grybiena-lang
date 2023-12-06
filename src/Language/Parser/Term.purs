module Language.Parser.Term where


import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.Cont (lift)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRec, tailRecM)
import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable, head, replicate)
import Data.CodePoint.Unicode (isUpper)
import Data.Functor.Mu (Mu)
import Data.Homogeneous (class ToHomogeneousRow)
import Data.Homogeneous.Record (fromHomogeneous, homogeneous)
import Data.List (List(..), (..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (codePointFromChar)
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Data.Tuple (Tuple(..), fst, uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Language.Kernel.Data (Data(..))
import Language.Kernel.Prim (primNatives)
import Language.Lambda.Calculus (absMany, app, appMany, cat, var)
import Language.Lambda.Inference (arrMany)
import Language.Lambda.Module (Module(..))
import Language.Lambda.Unification (class Fresh, TypingContext, fresh)
import Language.Native (Native(..), native)
import Language.Native.Module (Listing, NativeModule, moduleListing)
import Language.Native.Reify (nativeTerm, reify)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Basis (class StringParserT, class BasisParser)
import Language.Parser.Common (buildPostfixParser, languageDef)
import Language.Parser.Indent (IndentParserT, Positioned, block1, indented, runIndentT, withPos, withPos')
import Language.Term (Ident(..), Scope(..), TT(..), Term, Var(..))
import Parsing (fail, runParserT)
import Parsing.Combinators (choice, many, many1Till, try)
import Parsing.Expr (buildExprParser)
import Parsing.String (char, eof)
import Parsing.Token (GenTokenParser, makeTokenParser)
import Pretty.Printer (prettyPrint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

instance
  ( Fresh Int m
  , MonadState (TypingContext Var Mu Var TT) m
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
  | DataDecl DataTypeConstructor (List DataValueConstructor)

data DataTypeConstructor = DataTypeConstructor Var (List Var)
data DataValueConstructor = DataValueConstructor String (List Var)

dataConstructors :: DataTypeConstructor -> List DataValueConstructor -> List Decl
dataConstructors (DataTypeConstructor tycon tyvars) = tailRec go <<< Tuple Nil
  where
    dataType :: Term
    dataType = appMany (var tycon) (var <$> tyvars) 
    go (ds /\ Nil) = Done ds
    go (ds /\ (DataValueConstructor c ts):r) =
      let constructorType :: Term
          constructorType = arrMany (var <$> ts) dataType 
          nativeType :: Term
          nativeType = absMany tyvars constructorType 
          nativeTerm :: Data
          nativeTerm = DataConstructor c
          native :: Native Term
          native = Purescript { nativeType, nativeTerm: unsafeCoerce nativeTerm, nativePretty: c } 
          decl :: Decl 
          decl = ValueDecl (Ident $ TermVar c) (cat (Native native))
       in Loop ((decl:ds) /\ r)

instance Show Decl where
  show (TypeDecl v t) = prettyPrint v <> " :: " <> prettyPrint t
  show (ValueDecl v t) = prettyPrint v <> " = " <> prettyPrint t
  show (DataDecl (DataTypeConstructor t vs) cs) = "data " <> prettyPrint t

parser :: forall names row m.
          Fresh Int m
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
     
    parseModuleX :: (forall a. IndentParserT m a -> IndentParserT m (List a)) -> IndentParserT m (Module Var Term)
    parseModuleX f = do
      ls <- f (try parseDataDecl <|> try parseTypeDecl <|> parseValueDecl)
      ds <- tailRecM annotateVals (Nil /\ ls)
      pure $ Module (Map.fromFoldable ds)
      where
        annotateVals (d /\ Nil) = pure $ Done d
        annotateVals (d /\ ((ValueDecl v b):r)) = pure $ Loop (((v /\ b):d) /\ r)
        annotateVals (d /\ ((TypeDecl vt t):(ValueDecl vv v):r)) | vt == vv =
           pure $ Loop (((vv /\ (cat $ TypeAnnotation v t)):d) /\ r)
        annotateVals (_ /\ (TypeDecl vt _):r) = fail $ prettyPrint vt <> " type declaration not followed by value declaration. " <> show r
        annotateVals (d /\ ((DataDecl dtc z):r)) = pure $ Loop (d /\ (dataConstructors dtc z <> r))
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
           dtc <- parseDataTypeConstructor
           reservedOp "="
           fcon <- withPos parseDataValueConstructor
           dcons <- many (indented *> (reservedOp "|") *> withPos parseDataValueConstructor)
           pure (DataDecl dtc (fcon:dcons))
        parseDataTypeConstructor = do
           con <- parseTypeConstructor
           tvs <- many parseTypeVar
           pure (DataTypeConstructor con tvs)
        parseDataValueConstructor = do
           dcon <- parseDataConstructor'
           tvs <- many (indented *> parseTypeVar)
           pure $ DataValueConstructor dcon tvs




    parseTermVar :: Monad m => IndentParserT m Var
    parseTermVar = do
      i <- identifier 
      if Just false == ((isUpper <<< codePointFromChar) <$> (head $ toCharArray i))
        then pure $ Ident $ TermVar i
        else fail "Term variables must not start with an upper case char"

    parseDataConstructor :: Monad m => IndentParserT m Var
    parseDataConstructor = (Ident <<< TermVar) <$> parseDataConstructor'

    parseDataConstructor' :: Monad m => IndentParserT m String
    parseDataConstructor' = do
      i <- identifier 
      if Just true == ((isUpper <<< codePointFromChar) <$> (head $ toCharArray i))
        then pure i
        else fail "Data constructors must start with an upper case char"



    parseTypeVar :: Monad m => IndentParserT m Var
    parseTypeVar = do
      i <- identifier 
      if Just false == ((isUpper <<< codePointFromChar) <$> (head $ toCharArray i))
        then pure $ Ident $ TypeVar i
        else fail "Type variables must not start with an upper case char"

    parseTypeConstructor :: Monad m => IndentParserT m Var
    parseTypeConstructor = do
      i <- identifier 
      if Just true == ((isUpper <<< codePointFromChar) <$> (head $ toCharArray i))
        then pure $ Ident $ TypeVar i
        else fail "Type constructors must start with an upper case char"



    parseModuleB :: Monad m => IndentParserT m (Module Var Term)
    parseModuleB = parseModuleX (map List.fromFoldable <<< tokenParser.braces <<< tokenParser.semiSep1)

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
    parseValueAtom = defer $ \_ -> indented *> (parseAbs <|> parseNatives <|> (try (var <$> parseTermVar) <|> var <$> parseDataConstructor) <|> parseNumeric <|> parseTypeLit <|> parseLet <|> parseIfElse <|> (parens parseValue))
 
    
    parseTypeLit :: IndentParserT m Term
    parseTypeLit = char '@' *> ((cat <<< TypeLit) <$> parseTypeAtom)
    
    parseNumeric ::  IndentParserT m Term
    parseNumeric = (try parseNumber) <|> parseInt
    
    parseInt ::  IndentParserT m Term
    parseInt = cat <<< Native <<< (\i -> nativeTerm (show i) i) <$> integer
     
    parseNatives :: IndentParserT m Term
    parseNatives = choice $ map (uncurry parseNative) kernel
     
    parseNative ::  String -> IndentParserT m (Native Term) -> IndentParserT m Term
    parseNative name native = reserved name *> ((cat <<< Native) <$> native)
     
    parseNumber ::  IndentParserT m Term
    parseNumber = cat <<< Native <<< (\i -> nativeTerm (show i) i) <$> number 

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

    
    parseTypeAnnotation :: Term -> IndentParserT m Term
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
    

