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
import Language.Lambda.Block (Block(..))
import Language.Lambda.Calculus (absMany, app, cat, var)
import Language.Lambda.Unification (class Fresh, TypingContext, fresh)
import Language.Native (Native, native)
import Language.Native.Module (Listing, NativeModule, moduleListing)
import Language.Native.Reify (nativeTerm, reify)
import Language.Native.Unsafe (unsafeModule)
import Language.Parser.Basis (class StringParserT, class BasisParser)
import Language.Parser.Common (buildPostfixParser, languageDef)
import Language.Parser.Indent (IndentParserT, block1, block1Till, indented, runIndentT, withPos, withPos')
import Language.Term (Ident(..), Scope(..), TT(..), Term, Var(..))
import Parsing (runParserT)
import Parsing.Combinators (choice, many1Till, try)
import Parsing.Expr (buildExprParser)
import Parsing.String (char, eof)
import Parsing.Token (makeTokenParser)
import Type.Proxy (Proxy(..))

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
  , parseBlock :: Parser m (Block Var Term)
  }

parser :: forall names row m.
          Fresh Int m
       => MonadState (TypingContext Var Mu Var TT) m
       => ToHomogeneousRow names (IndentParserT m (Native Term)) row
       => NativeModule names (IndentParserT m (Native Term))
       -> TermParser m
parser mod = {
    parseValue: Parser parseValue
  , parseType: Parser parseType
  , parseBlock: Parser parseBlock
  }
  where
    kernel :: Listing (IndentParserT m (Native Term))
    kernel = moduleListing mod


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
    
    parseBlock :: IndentParserT m (Block Var Term)
    parseBlock = do
      ds <- tokenParser.braces (tokenParser.semiSep1 parseValueDecl)
      pure $ Block (Map.fromFoldable ds)
      where
        parseValueDecl = do
           v <- ((Ident <<< TermVar) <$> identifier) 
           reservedOp "="
           b <- parseValue
           pure (v /\ b)

    parseLet :: IndentParserT m Term
    parseLet = (try parseLetB) <|> parseLetI 
      where
        parseLetI :: IndentParserT m Term
        parseLetI = do
          l <- withPos' (reserved "let") do
             indented
             block1Till parseValueDecl (reserved "in")

          body <- parseValue
          pure $ cat $ Let (Block (Map.fromFoldable l)) body
          where
            parseValueDecl = do
               v <- ((Ident <<< TermVar) <$> identifier) 
               reservedOp "="
               b <- parseValueI
               pure (v /\ b)
    
        parseLetB :: IndentParserT m Term
        parseLetB = do
          reserved "let"
          b <- parseBlock
          reserved "in"
          body <- parseValue
          pure $ cat $ Let b body

    parseValueI :: Monad m => IndentParserT m Term
    parseValueI = indented *> (buildExprParser [] (buildPostfixParser [parseAppI, parseTypeAnnotation] parseValueAtomI)) 
    
    parseValueAtomI :: IndentParserT m Term
    parseValueAtomI = defer $ \_ -> indented *> (parseAbsI <|> parseNatives <|> ((var <<< Ident <<< TermVar) <$> identifier) <|> parseNumeric <|> parseTypeLit <|> parseLet <|> parseIfElse <|> (parens parseValueI))
 

    parseValue :: Monad m => IndentParserT m Term
    parseValue = buildExprParser [] (buildPostfixParser [parseApp, parseTypeAnnotation] parseValueAtom) 
    
    parseValueAtom :: IndentParserT m Term
    parseValueAtom = defer $ \_ -> parseAbs <|> parseNatives <|> ((var <<< Ident <<< TermVar) <$> identifier) <|> parseNumeric <|> parseTypeLit <|> parseLet <|> parseIfElse <|> (parens parseValue)
    
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
 
    parseAbsI :: IndentParserT m Term
    parseAbsI = absMany <$> parsePats <*> parseValueI
      where
        parsePats = reservedOp "\\" *> many1Till (Ident <<< TermVar <$> identifier) (reservedOp "->")
    
    parseAppI :: Term -> IndentParserT m Term
    parseAppI v = app v <$> parseValueAtomI 

    parseAbs :: IndentParserT m Term
    parseAbs = absMany <$> parsePats <*> parseValue
      where
        parsePats = reservedOp "\\" *> many1Till (Ident <<< TermVar <$> identifier) (reservedOp "->")
    
    parseApp :: Term -> IndentParserT m Term
    parseApp v = app v <$> parseValueAtom
    
    parseType :: Monad m => IndentParserT m Term
    parseType = buildPostfixParser [parseTypeArrow, parseTypeApp, parseTypeAnnotation] parseTypeAtom 
    
    parseTypeAtom :: IndentParserT m Term
    parseTypeAtom = defer $ \_ -> parseTypeAbs <|> ((var <<< Ident <<< TypeVar) <$> identifier) <|> parseStar <|> parseTypeInt <|> parseTypeNumber <|> parseTypeEffect <|> (parens parseType)
    
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
    

