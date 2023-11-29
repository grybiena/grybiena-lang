module Language.Parser.Term where


import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.Cont (lift)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable, replicate)
import Data.Functor.Mu (Mu)
import Data.Homogeneous (class ToHomogeneousRow)
import Data.Homogeneous.Record (fromHomogeneous, homogeneous)
import Data.List ((..))
import Data.Map as Map
import Data.String.CodeUnits (fromCharArray)
import Data.Tuple (fst, uncurry)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Language.Kernel.Prim (primNatives)
import Language.Lambda.Calculus (absMany, app, cat, var)
import Language.Lambda.Unification (class Fresh, TypingContext, fresh)
import Language.Native (Native, native)
import Language.Native.Module (Listing, NativeModule, moduleListing)
import Language.Native.Reify (nativeTerm, reify)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Basis (class StringParserT, class BasisParser)
import Language.Parser.Common (buildPostfixParser, languageDef)
import Language.Term (Ident(..), Scope(..), TT(..), Term, Var(..))
import Parsing (ParserT, runParserT)
import Parsing.Combinators (choice, many1Till, try)
import Parsing.Expr (buildExprParser)
import Parsing.String (char, eof)
import Parsing.Token (GenTokenParser, makeTokenParser)
import Type.Proxy (Proxy(..))

instance
  ( MonadState (TypingContext Var Mu Var TT) m
  ) => BasisParser Parser m Mu Var TT where
  parseBasis = do
    t <- (parser (homogeneous {})).parseType
    Parser eof
    pure t

instance MonadRec m => StringParserT Parser m where
  runStringParserT s (Parser p) = runParserT s p

newtype Parser m a = Parser (ParserT String m a)
derive newtype instance Functor (Parser m)
derive newtype instance Apply (Parser m)
derive newtype instance Applicative (Parser m)
derive newtype instance Bind (Parser m)
derive newtype instance Monad m => Monad (Parser m)

type TermParser m =
  { parseValue:: Parser m Term
  , parseType :: Parser m Term
  }

parser :: forall names row m.
          Fresh Int m
       => MonadState (TypingContext Var Mu Var TT) m
       => ToHomogeneousRow names (ParserT String m (Native Term)) row
       => NativeModule names (ParserT String m (Native Term))
       -> TermParser m
parser mod = {
    parseValue: Parser parseValue
  , parseType: Parser parseType
  }
  where
    kernel :: Listing (ParserT String m (Native Term))
    kernel = moduleListing mod

    tokenParser :: GenTokenParser String m 
    tokenParser = makeTokenParser (languageDef (fromFoldable (fst <$> kernel)))

    integer :: ParserT String m Int
    integer = tokenParser.integer 
    
    number :: ParserT String m Number
    number = tokenParser.float
    
    reservedOp :: String -> ParserT String m Unit
    reservedOp = tokenParser.reservedOp
     
    reserved :: String -> ParserT String m Unit
    reserved = tokenParser.reserved

    identifier :: ParserT String m String
    identifier = tokenParser.identifier
        
    parens :: forall a. ParserT String m a -> ParserT String m a
    parens = tokenParser.parens
    
    parseLet :: ParserT String m Term
    parseLet = do
      reserved "let"
      ds <- tokenParser.braces (tokenParser.semiSep1 parseValueDecl)
      reserved "in"
      body <- parseValue
      pure $ cat $ Let (Map.fromFoldable ds) body
      where
        parseValueDecl = do
           v <- ((Ident <<< TermVar) <$> identifier) 
           reservedOp "="
           b <- parseValue
           pure (v /\ b)


    parseValue :: Monad m => ParserT String m Term
    parseValue = buildExprParser [] (buildPostfixParser [parseApp, parseTypeAnnotation] parseValueAtom) 
    
    parseValueAtom :: ParserT String m Term
    parseValueAtom = defer $ \_ -> parseAbs <|> parseNatives <|> ((var <<< Ident <<< TermVar) <$> identifier) <|> parseNumeric <|> parseTypeLit <|> parseLet <|> parseIfElse <|> (parens parseValue)
    
    parseTypeLit :: ParserT String m Term
    parseTypeLit = char '@' *> ((cat <<< TypeLit) <$> parseTypeAtom)
    
    parseNumeric ::  ParserT String m Term
    parseNumeric = (try parseNumber) <|> parseInt
    
    parseInt ::  ParserT String m Term
    parseInt = cat <<< Native <<< (\i -> nativeTerm (show i) i) <$> integer
     
    parseNatives :: ParserT String m Term
    parseNatives = choice $ map (uncurry parseNative) kernel
     
    parseNative ::  String -> ParserT String m (Native Term) -> ParserT String m Term
    parseNative name native = reserved name *> ((cat <<< Native) <$> native)
     
    parseNumber ::  ParserT String m Term
    parseNumber = cat <<< Native <<< (\i -> nativeTerm (show i) i) <$> number 

    parseIfElse :: ParserT String m Term
    parseIfElse = do
      reserved "if"
      x <- parseValue
      reserved "then"
      a <- parseValue
      reserved "else"
      b <- parseValue
      i <- native <$> (fromHomogeneous (unsafeModule (Proxy :: Proxy Parser) primNatives))."ifElse"
      pure $ app (app (app i x) a) b

    
    parseTypeAnnotation :: Term -> ParserT String m Term
    parseTypeAnnotation v = do
      reservedOp "::"
      t <- parseType
      pure $ cat $ TypeAnnotation v t
     
    parseAbs :: ParserT String m Term
    parseAbs = absMany <$> parsePats <*> parseValue
      where
        parsePats = reservedOp "\\" *> many1Till (Ident <<< TermVar <$> identifier) (reservedOp "->")
    
    parseApp :: Term -> ParserT String m Term
    parseApp v = app v <$> parseValueAtom
    
    parseType :: Monad m => ParserT String m Term
    parseType = buildPostfixParser [parseTypeArrow, parseTypeApp, parseTypeAnnotation] parseTypeAtom 
    
    parseTypeAtom :: ParserT String m Term
    parseTypeAtom = defer $ \_ -> parseTypeAbs <|> ((var <<< Ident <<< TypeVar) <$> identifier) <|> parseStar <|> parseTypeInt <|> parseTypeNumber <|> parseTypeEffect <|> (parens parseType)
    
    parseTypeInt ::  ParserT String m Term
    parseTypeInt = reserved "Int" *> pure (reify (Proxy :: Proxy Int))
     
    parseTypeNumber :: ParserT String m Term
    parseTypeNumber = reserved "Number" *> pure (reify (Proxy :: Proxy Number))
      
    parseTypeEffect ::  ParserT String m Term
    parseTypeEffect = reserved "Effect" *> pure (reify (Proxy :: Proxy Effect))
    
    
    parseTypeArrow :: Term -> ParserT String m Term
    parseTypeArrow a = do
      reservedOp "->"
      b <- parseType
      pure (app (app (cat Arrow) a) b)
    
    parseStar ::  ParserT String m Term
    parseStar = choice (star <$> (1 .. 4))
      where
        star i = do
          reservedOp (fromCharArray (replicate i '*'))
          pure $ cat (Star i)
    
    parseTypeAbs :: ParserT String m Term
    parseTypeAbs = absMany <$> parsePats <*> parseType
      where
        parsePats = reservedOp "forall" *> many1Till scopedVar (reservedOp ".")
        scopedVar = do
          i <- identifier
          s <- lift fresh
          pure $ Scoped (TypeVar i) (Scope s)
    
    parseTypeApp :: Term -> ParserT String m Term
    parseTypeApp v = app v <$> parseTypeAtom
    

