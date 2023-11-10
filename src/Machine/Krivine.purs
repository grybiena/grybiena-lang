module Machine.Krivine where

-- For a description of Krivine Machines see this article
-- https://www.pls-lab.org/en/Krivine_machine

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..), maybe)
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (LambdaF(..))
import Machine.Closure (Closure(..), closure)
import Machine.Context (class Context, binds, bound)
import Matryoshka.Class.Recursive (class Recursive, project)


-- | Evaluates of the Category `cat` over the Lambda calculus
class Applicative m <= Evaluate f var cat m where
  -- | thunk elimination
  thunk :: cat (f (LambdaF var cat)) -> m (cat Void) 
  -- | functor application
  functor :: cat (f (LambdaF var cat)) -> cat Void -> m (f (LambdaF var cat)) 


-- | The transitions of a Machine are defined by the Category over which the Lambdas abstract
class Transition f var cat ctx halt m where
  transition :: cat (f (LambdaF var cat))
             -> Maybe (Machine f var cat ctx)
             -> m (Step (Machine f var cat ctx) (Halt var halt))

instance
  ( MonadRec m
  , Context var (Closure f var cat ctx) ctx
  , Recursive (f (LambdaF var cat)) (LambdaF var cat)
  , Evaluate f var cat m
  ) => Transition f var cat ctx (cat Void) m where
  transition o Nothing = (Done <<< Halt) <$> thunk o
  transition f (Just stack) = do
     let arg@(Closure (_ /\ ctx)) = head stack
     res <- evalUnbounded arg
     case res of
       Halt h -> do
         aft <- functor f h
         pure $ Loop ((closure aft ctx) :< tail stack)
       err -> pure $ Done err

-- | A Machine is a non-empty Stack of Closures
type Machine f var cat ctx = Cofree Maybe (Closure f var cat ctx)

-- | A Machine Halts either because of a fault in the Lambda calculus or
-- because a transition results in a halting condition
data Halt var halt =
    ContextFault var
  | StackFault
  | Halt halt

derive instance Generic (Halt var halt) _
instance (Show var, Show halt) => Show (Halt var halt) where
  show = genericShow
instance (Eq var, Eq halt) => Eq (Halt var halt) where
  eq = genericEq

-- | A Krivine Machine Step
-- Abs ~ pop, bind, and evaluate the body
-- App ~ push the argument and evaluate the applied term
-- Var ~ dereference the variable
-- Cat ~ evaluate a state transition
step :: forall f var cat ctx halt m .
        Monad m
     => Context var (Closure f var cat ctx) ctx
     => Recursive (f (LambdaF var cat)) (LambdaF var cat)
     => Transition f var cat ctx halt m
     => Machine f var cat ctx -> m (Step (Machine f var cat ctx) (Halt var halt))
step machine = do
  let Closure (term /\ context) = head machine
  case project term of
    Abs var body ->
      case tail machine of
        Nothing -> pure $ Done StackFault
        Just stack -> do
          pure $ Loop $ (closure body (binds var (head stack) context)) :< tail stack 
    App f g ->
      pure $ Loop $ (closure f context) :< Just ((closure g context) :< tail machine)
    Var var -> do
      let continue closure = closure :< tail machine
      pure $ maybe (Done $ ContextFault var) (Loop <<< continue) (bound var context)
    Cat c -> transition c (tail machine)

-- | Run a Krivine machine until a Halting condition is reached
runUnbounded :: forall f var cat ctx halt m .
                MonadRec m
             => Context var (Closure f var cat ctx) ctx
             => Recursive (f (LambdaF var cat)) (LambdaF var cat)
             => Transition f var cat ctx halt m
             => Machine f var cat ctx -> m (Halt var halt)
runUnbounded = tailRecM step


evalUnbounded :: forall f var cat ctx halt m .
                 MonadRec m
              => Context var (Closure f var cat ctx) ctx
              => Recursive (f (LambdaF var cat)) (LambdaF var cat)
              => Transition f var cat ctx halt m
              => Closure f var cat ctx -> m (Halt var halt)
evalUnbounded c = runUnbounded (c :< Nothing)

