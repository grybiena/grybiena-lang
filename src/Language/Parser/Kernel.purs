module Language.Parser.Kernel where


import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.Cont (lift)
import Data.Array (fromFoldable, replicate)
import Data.List (List, (..))
import Data.String.CodeUnits (fromCharArray)
import Data.Tuple (uncurry)
import Language.Grybu (Ident(..), Scope(..), TT(..), Term, Var(..))
import Language.Kernel.Library (Kernel, compileKernel, kernelLibraryUnion, kernelStrings)
import Language.Kernel.Library.Effect (EffectTermListing, effectNatives)
import Language.Kernel.Library.Pure (PureTermListing, pureNatives)
import Language.Lambda.Calculus (absMany, app, cat, var)
import Language.Lambda.Unification (class Fresh, fresh)
import Language.Parser.Common (buildPostfixParser, languageDef)
import Language.Type.Reify (reifyNative)
import Language.Value.Native (Native)
import Parsing (ParserT)
import Parsing.Combinators (choice, many1Till, try)
import Parsing.Expr (buildExprParser)
import Parsing.String (char)
import Parsing.Token (GenTokenParser, makeTokenParser)
import Type.Proxy (Proxy(..))

kernel :: forall m n. Monad m => Fresh Int m => Monad n => Kernel (m (Native (Term n)))
kernel = compileKernel $ kernelLibraryUnion pureNatives effectNatives

reservedKernelNames :: List String
reservedKernelNames = kernelStrings (Proxy :: Proxy PureTermListing)
                   <> kernelStrings (Proxy :: Proxy EffectTermListing)

tokenParser :: forall m . Monad m => GenTokenParser String m 
tokenParser = makeTokenParser (languageDef (fromFoldable reservedKernelNames))

integer :: forall m . Monad m => ParserT String m Int
integer = tokenParser.integer 

number :: forall m . Monad m => ParserT String m Number
number = tokenParser.float

reservedOp :: forall m. Monad m => String -> ParserT String m Unit
reservedOp = tokenParser.reservedOp

commaSep :: forall m a. Monad m => ParserT String m a -> ParserT String m (List a)
commaSep = tokenParser.commaSep

reserved :: forall m. Monad m => String -> ParserT String m Unit
reserved = tokenParser.reserved

identifier :: forall m. Monad m => ParserT String m String
identifier = tokenParser.identifier

operator :: forall m. Monad m => ParserT String m String
operator = tokenParser.operator

stringLiteral :: forall m. Monad m => ParserT String m String
stringLiteral = tokenParser.stringLiteral

lexeme :: forall m a. Monad m => ParserT String m a -> ParserT String m a
lexeme = tokenParser.lexeme

brackets :: forall m a. Monad m => ParserT String m a -> ParserT String m a
brackets = tokenParser.brackets

braces :: forall m a. Monad m => ParserT String m a -> ParserT String m a
braces = tokenParser.braces

parens :: forall m a. Monad m => ParserT String m a -> ParserT String m a
parens = tokenParser.parens



parseValue :: forall m n. Monad m => Fresh Int m => Fresh Var m => Monad n => ParserT String m (Term n)
parseValue = buildExprParser [] (buildPostfixParser [parseApp, parseTypeAnnotation] parseValueAtom) 

parseValueAtom :: forall m n. Monad m => Fresh Int m => Fresh Var m => Monad n => ParserT String m (Term n)
parseValueAtom = defer $ \_ -> parseAbs <|> ((var <<< Ident <<< TermVar) <$> identifier) <|> parseNumeric <|> parseNatives <|> parseTypeLit <|> (parens parseValue)

parseTypeLit :: forall m n. Fresh Int m => Monad m => ParserT String m (Term n)
parseTypeLit = char '@' *> parseTypeAtom 

parseNumeric :: forall m n. Monad m => ParserT String m (Term n)
parseNumeric = (try parseNumber) <|> parseInt

parseInt :: forall m n. Monad m => ParserT String m (Term n)
parseInt = cat <<< Native <<< reifyNative <$> integer
 
parseNatives :: forall m n. Monad m => Fresh Int m => Monad n => ParserT String m (Term n)
parseNatives = choice $ map (uncurry parseNative) kernel
 
parseNative :: forall m n. Monad m => String -> m (Native (Term n)) -> ParserT String m (Term n)
parseNative name native = reserved name *> ((cat <<< Native) <$> lift native)
 
parseNumber :: forall m n. Monad m => ParserT String m (Term n)
parseNumber = cat <<< Native <<< reifyNative <$> number 

parseTypeAnnotation :: forall m n. Fresh Int m => Monad m => (Term n) -> ParserT String m (Term n)
parseTypeAnnotation v = do
  reservedOp "::"
  t <- parseType
  pure $ cat $ TypeAnnotation v t
 
parseAbs :: forall m n. Monad m => Fresh Var m => Fresh Int m => Monad n => ParserT String m (Term n)
parseAbs = absMany <$> parsePats <*> parseValue
  where
    parsePats = reservedOp "\\" *> many1Till (Ident <<< TermVar <$> identifier) (reservedOp "->")

parseApp :: forall m n. Monad m => Fresh Var m => Fresh Int m => Monad n => (Term n) -> ParserT String m (Term n)
parseApp v = app v <$> parseValueAtom

parseType :: forall m n. Fresh Int m => Monad m => ParserT String m (Term n)
parseType = buildPostfixParser [parseTypeArrow, parseTypeApp, parseTypeAnnotation] parseTypeAtom 

parseTypeAtom :: forall m n. Fresh Int m => Monad m => ParserT String m (Term n)
parseTypeAtom = defer $ \_ -> parseTypeAbs <|> ((var <<< Ident <<< TypeVar) <$> identifier) <|> parseStar <|> parseTypeInt <|> parseTypeNumber <|> parseTypeEffect <|> (parens parseType)

parseTypeInt :: forall m n . Monad m => ParserT String m (Term n)
parseTypeInt = reserved "Int" *> pure (cat TypeInt)
 
parseTypeNumber :: forall m n . Monad m => ParserT String m (Term n)
parseTypeNumber = reserved "Number" *> pure (cat TypeNumber)
  
parseTypeEffect :: forall m n . Monad m => ParserT String m (Term n)
parseTypeEffect = reserved "Effect" *> pure (cat TypeEffect)


parseTypeArrow :: forall m n. Fresh Int m => Monad m => (Term n) -> ParserT String m (Term n)
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

parseTypeAbs :: forall m n. Fresh Int m => Monad m => ParserT String m (Term n)
parseTypeAbs = absMany <$> parsePats <*> parseType
  where
    parsePats = reservedOp "forall" *> many1Till scopedVar (reservedOp ".")
    scopedVar = do
      i <- identifier
      s <- lift fresh
      pure $ Scoped (TypeVar i) (Scope s)

parseTypeApp :: forall m n. Fresh Int m => Monad m => (Term n) -> ParserT String m (Term n)
parseTypeApp v = app v <$> parseTypeAtom




