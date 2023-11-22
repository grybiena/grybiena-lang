module Language.Parser.Term where


import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.Cont (lift)
import Data.Array (fromFoldable, replicate)
import Data.Homogeneous (class ToHomogeneousRow)
import Data.List ((..))
import Data.Map as Map
import Data.String.CodeUnits (fromCharArray)
import Data.Tuple (fst, uncurry)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Language.Lambda.Calculus (absMany, app, cat, var)
import Language.Lambda.Unification (class Fresh, fresh)
import Language.Native.Module (Listing, NativeModule, moduleListing)
import Language.Parser.Common (buildPostfixParser, languageDef)
import Language.Term (Ident(..), Scope(..), TT(..), Term, Var(..))
import Language.Native.Reify (nativeTerm, reify)
import Language.Native (Native)
import Parsing (ParserT)
import Parsing.Combinators (choice, many1Till, try)
import Parsing.Expr (buildExprParser)
import Parsing.String (char)
import Parsing.Token (GenTokenParser, makeTokenParser)
import Type.Proxy (Proxy(..))

type Parser m =
  { parseValue:: ParserT String m Term
  , parseType :: ParserT String m Term
  }

parser :: forall names row m.
          Fresh Int m
       => ToHomogeneousRow names (ParserT String m (Native Term)) row
       => NativeModule names (ParserT String m (Native Term))
       -> Parser m
parser mod = {
    parseValue: parseValue
  , parseType: parseType
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
    
    parseLetRec :: ParserT String m Term
    parseLetRec = do
      reserved "let"
      ds <- tokenParser.braces (tokenParser.semiSep1 parseValueDecl)
      reserved "in"
      body <- parseValue
      pure $ cat $ LetRec (Map.fromFoldable ds) body
      where
        parseValueDecl = do
           v <- ((Ident <<< TermVar) <$> identifier) 
           reservedOp "="
           b <- parseValue
           pure (v /\ b)


    parseValue :: Monad m => ParserT String m Term
    parseValue = buildExprParser [] (buildPostfixParser [parseApp, parseTypeAnnotation] parseValueAtom) 
    
    parseValueAtom :: ParserT String m Term
    parseValueAtom = defer $ \_ -> parseAbs <|> parseNatives <|> ((var <<< Ident <<< TermVar) <$> identifier) <|> parseNumeric <|> parseTypeLit <|> parseLetRec <|> (parens parseValue)
    
    parseTypeLit :: ParserT String m Term
    parseTypeLit = char '@' *> parseTypeAtom 
    
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
    

