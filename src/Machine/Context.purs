module Machine.Context where

import Control.Alt (class Functor, (<$>))
import Control.Category ((<<<))
import Control.Comonad (class Comonad, class Extend, extract)
import Control.Comonad.Store (class ComonadStore)
import Control.Comonad.Trans.Class (class ComonadTrans)
import Control.Extend ((<<=))
import Data.Function (($))
import Data.Function.Memoize (class Tabulate, memoize)
import Data.Identity (Identity(..))
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (type (/\), (/\))

type Context s = ContextT s Identity

runContext :: forall s a. Context s a -> (s -> a) /\ s 
runContext (ContextT (Identity f /\ s)) = f /\ s

context :: forall s a. (s -> a) -> s -> Context s a
context f s = ContextT (Identity f /\ s)

newtype ContextT s w a = ContextT ((w (s -> a)) /\ s)

runContextT :: forall s w a . ContextT s w a -> ((w (s -> a)) /\ s)
runContextT (ContextT ctx) = ctx
 
derive instance Newtype (ContextT s w a) _

instance
  ( Tabulate s
  , Functor w
  ) => Functor (ContextT s w) where
  map f (ContextT (w /\ s)) = ContextT (((\g -> memoize (f <<< g)) <$> w) /\ s)

instance
  ( Tabulate s
  , Extend w
  ) => Extend (ContextT s w) where
  extend f (ContextT (w /\ s)) = ContextT (((\w' s' -> f (ContextT (w' /\ s'))) <<= w) /\ s)

instance
  ( Tabulate s
  , Comonad w
  ) => Comonad (ContextT s w) where
  extract (ContextT (w /\ a)) = extract w a

instance ComonadTrans (ContextT s) where
  lower (ContextT (w /\ s)) = (_ $ s) <$> w

instance
  ( Tabulate s
  , Comonad w
  ) => ComonadStore s (ContextT s w) where
  pos (ContextT (_ /\ s)) = s
  peek s (ContextT (f /\ _)) = extract f s


