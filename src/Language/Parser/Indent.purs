module Language.Parser.Indent 
  ( IndentParserT
  , Positioned
  , runIndentT
  , withBlock
  , withBlock'
  , block
  , block1
  , block1Till
  , indented
  , indented'
  , sameLine
  , sameOrIndented
  , checkIndent
  , withPos
  , withPos'
  , indentAp
  , (<+/>)
  , indentNoAp
  , (<-/>)
  , indentMany
  , (<*/>)
  , indentOp
  , (<?/>)
  , indentBrackets
  , indentAngles
  , indentBraces
  , indentParens
  , Optional(..)
  ) where
-- modified version of https://github.com/purescript-contrib/purescript-parsing/blob/v10.2.0/src/Parsing/Indent.purs

import Prelude

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Control.Monad.Cont (class MonadTrans)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (class MonadState, StateT, evalStateT, state)
import Control.Monad.State.Trans (get, put)
import Control.Monad.Trans.Class (lift)
import Data.List (List(..), many)
import Data.List.NonEmpty (NonEmptyList)
import Data.Maybe (Maybe(..))
import Parsing (ParserT, fail, position, Position(..), initialPos)
import Parsing.Combinators (many1Till, option, optionMaybe)
import Parsing.String (string)
import Parsing.String.Basic (oneOf)

newtype Positioned m a = Positioned (StateT Position m a)
derive newtype instance Monad m => Functor (Positioned m)
derive newtype instance Monad m => Apply (Positioned m)
derive newtype instance Monad m => Applicative (Positioned m)
derive newtype instance Monad m => Bind (Positioned m)
derive newtype instance Monad m => Monad (Positioned m)
derive newtype instance MonadRec m => MonadRec (Positioned m)
instance MonadTrans Positioned where
  lift = Positioned <<< lift
instance MonadState s m => MonadState s (Positioned m) where
  state = lift <<< state

type IndentParserT m a = ParserT String (Positioned m) a

-- | Run the result of an indentation sensitive parse
runIndentT :: forall m a. Functor m => Positioned m a -> m a
runIndentT (Positioned f) = evalStateT f initialPos

get' :: forall m. Monad m => IndentParserT m Position
get' = do
  g <- lift (Positioned get)
  pure g

put' :: forall m. Monad m => Position -> IndentParserT m Unit
put' p = lift (Positioned (put p))

many1 :: forall s m a. ParserT s m a -> ParserT s m (List a)
many1 p = lift2 Cons p (many p)

symbol :: forall m. String -> ParserT String m String
symbol name = (many $ oneOf [ ' ', '\t' ]) *> (string name)

-- | Parses using the current location for indentation reference
withPos :: forall m a. Monad m => IndentParserT m a -> IndentParserT m a
withPos x = do
  a <- get'
  p <- position
  r <- put' p *> x
  put' a *> pure r

-- | Parses using the current location for indentation reference
withPos' :: forall m a e. Monad m => IndentParserT m e -> IndentParserT m a -> IndentParserT m a
withPos' f x = do
  a <- get'
  p <- position
  _ <- f
  r <- put' p *> x
  put' a *> pure r



-- | Parses only when indented past the level of the reference
indented :: forall m. Monad m => IndentParserT m Unit
indented = do
  Position p <- position
  Position s <- get'
  if p.column <= s.column then fail "not indented"
  else put' $ Position { index: 0, line: p.line, column: s.column }

-- | Same as `indented`, but does not change internal state
indented' :: forall m. Monad m => IndentParserT m Unit
indented' = do
  Position p <- position
  Position s <- get'
  if p.column <= s.column then fail "not indented" else pure unit

-- | Ensures the current indentation level matches that of the reference
checkIndent :: forall m. Monad m => IndentParserT m Unit
checkIndent = do
  Position p <- position
  Position s <- get'
  if p.column == s.column then pure unit else fail ("indentation doesn't match " <> show p <> " /= " <> show s)


-- | Parses a block of lines at the same indentation level , empty Blocks allowed
block :: forall m a. Monad m => IndentParserT m a -> IndentParserT m (List a)
block p = withPos $ do
  r <- many $ checkIndent *> p
  pure r


-- | Parses a block of lines at the same indentation level
block1 :: forall m a. Monad m => IndentParserT m a -> IndentParserT m (List a)
block1 p = withPos $ do
  r <- many1 $ checkIndent *> p
  pure r


-- | Parses a block of lines at the same indentation level
block1Till :: forall m a e. Monad m => IndentParserT m a -> IndentParserT m e -> IndentParserT m (NonEmptyList a)
block1Till p t = withPos $ do
  r <- many1Till (checkIndent *> p) t
  pure r

-- | `withBlock f a p` parses `a`
-- | followed by an indented block of `p`
-- | combining them with `f`.
withBlock :: forall a b c m. Monad m => (a -> List b -> c) -> IndentParserT m a -> IndentParserT m b -> IndentParserT m c
withBlock f a p = withPos $ do
  r1 <- a
  r <- optionMaybe $ indented *> block p
  case r of
    Nothing -> pure (f r1 Nil)
    Just r2 -> pure (f r1 r2)

-- | Like 'withBlock', but throws away initial parse result
withBlock' :: forall a b m. Monad m => IndentParserT m a -> IndentParserT m b -> IndentParserT m (List b)
withBlock' = withBlock (flip const)

-- | Parses only on the same line as the reference
sameLine :: forall m. Monad m => IndentParserT m Unit
sameLine = do
  Position p <- position
  Position s <- get'
  if p.line == s.line then pure unit else fail "over one line"

-- | Parses only when indented past the level of the reference or on the same line
sameOrIndented :: forall m. Monad m => IndentParserT m Unit
sameOrIndented = sameLine <|> indented

-- | `<+/>` is to indentation sensitive parsers what `ap` is to monads
indentAp :: forall m a b. Monad m => IndentParserT m (a -> b) -> IndentParserT m a -> IndentParserT m b
indentAp a b = ap a $ sameOrIndented *> b

infixl 9 indentAp as <+/>

-- | Like `<+/>` but doesn't apply the function to the parsed value
indentNoAp :: forall m a b. Monad m => IndentParserT m a -> IndentParserT m b -> IndentParserT m a
indentNoAp a b = lift2 const a $ sameOrIndented *> b

infixl 10 indentNoAp as <-/>

-- | Like `<+/>` but applies the second parser many times
indentMany :: forall m a b. Monad m => IndentParserT m (List a -> b) -> IndentParserT m a -> IndentParserT m b
indentMany a b = ap a (many (sameOrIndented *> b))

infixl 11 indentMany as <*/>

-- | Data type used to optional parsing
data Optional m a = Opt a (IndentParserT m a)

-- | Like `<+/>` but applies the second parser optionally using the `Optional` datatype
indentOp :: forall m a b. Monad m => IndentParserT m (a -> b) -> Optional m a -> IndentParserT m b
indentOp a (Opt b c) = ap a (option b (sameOrIndented *> c))

infixl 12 indentOp as <?/>

-- | Parses with surrounding brackets
indentBrackets :: forall m a. Monad m => IndentParserT m a -> IndentParserT m a
indentBrackets p = withPos $ pure identity <-/> symbol "[" <+/> p <-/> symbol "]"

-- | Parses with surrounding angle brackets
indentAngles :: forall m a. Monad m => IndentParserT m a -> IndentParserT m a
indentAngles p = withPos $ pure identity <-/> symbol "<" <+/> p <-/> symbol ">"

-- | Parses with surrounding braces
indentBraces :: forall m a. Monad m => IndentParserT m a -> IndentParserT m a
indentBraces p = withPos $ pure identity <-/> symbol "{" <+/> p <-/> symbol "}"

-- | Parses with surrounding parentheses
indentParens :: forall m a. Monad m => IndentParserT m a -> IndentParserT m a
indentParens p = withPos $ pure identity <-/> symbol "(" <+/> p <-/> symbol ")"

