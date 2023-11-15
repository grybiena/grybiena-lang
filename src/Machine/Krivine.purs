module Machine.Krivine where

-- For a description of MachineFault Machines see this article
-- https://www.pls-lab.org/en/MachineFault_machine

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Maybe (Maybe(..), maybe)
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (LambdaF(..))
import Machine.Closure (Closure(..), closure)
import Machine.Context (class Context, binds, bound)
import Matryoshka.Class.Recursive (class Recursive, project)

-- | A Machine is a non-empty Stack of Closures
type Machine f var cat ctx = Cofree Maybe (Closure f var cat ctx)

-- | A Machine either requires further evaluation or results in an element
-- of the category Void of lambdas
type MachineStep f var cat ctx = Step (Machine f var cat ctx) (cat Void)

-- | A Machine can reach a fault condition in which the Krivine reduction
-- rules do not have defined behaviour. That behaviour is defined by this class.
class MachineFault f var cat ctx m where
  contextFault :: Machine f var cat ctx -> var -> m (MachineStep f var cat ctx) 
  stackFault :: var -> f (LambdaF var cat) -> m (MachineStep f var cat ctx) 

-- | Evaluates of the Category `cat` over the Lambda calculus
class Applicative m <= Evaluate f var cat m where
  -- | thunk elimination
  thunk :: cat (f (LambdaF var cat)) -> m (cat Void) 
  -- | functor application
  functor :: cat (f (LambdaF var cat)) -> cat Void -> m (f (LambdaF var cat)) 

-- | Transitions defined by evaluation of the category
transition :: forall m f var cat ctx.
              MonadRec m
           => Context var (Closure f var cat ctx) ctx
           => Recursive (f (LambdaF var cat)) (LambdaF var cat)
           => Evaluate f var cat m
           => MachineFault f var cat ctx m
           =>  cat (f (LambdaF var cat))
           -> Maybe (Machine f var cat ctx)
           -> m (MachineStep f var cat ctx)
transition o Nothing = Done <$> thunk o
transition f (Just stack) = do
   let arg@(Closure (_ /\ ctx)) = head stack
   res <- evalUnbounded arg
   aft <- functor f res
   pure $ Loop ((closure aft ctx) :< tail stack)

-- | A MachineFault Machine Step
-- Abs ~ pop, bind, and evaluate the body
-- App ~ push the argument and evaluate the applied term
-- Var ~ dereference the variable
-- Cat ~ evaluate a state transition
step :: forall f var cat ctx m.
        MonadRec m
     => Context var (Closure f var cat ctx) ctx
     => Recursive (f (LambdaF var cat)) (LambdaF var cat)
     => Evaluate f var cat m
     => MachineFault f var cat ctx m
     => Machine f var cat ctx -> m (MachineStep f var cat ctx)
step machine = do
  let Closure (term /\ context) = head machine
  case project term of
    Abs var body ->
      case tail machine of
        Nothing -> stackFault var body
        Just stack -> do
          pure $ Loop $ (closure body (binds var (head stack) context)) :< tail stack 
    App f g ->
      pure $ Loop $ (closure f context) :< Just ((closure g context) :< tail machine)
    Var var -> do
      let continue closure = closure :< tail machine
      maybe (contextFault machine var) (pure <<< Loop <<< continue) (bound var context)
    Cat c -> transition c (tail machine)

-- | Run a MachineFault machine until a Halting condition is reached
runUnbounded :: forall f var cat ctx m .
                MonadRec m
             => Context var (Closure f var cat ctx) ctx
             => Recursive (f (LambdaF var cat)) (LambdaF var cat)
             => Evaluate f var cat m
             => MachineFault f var cat ctx m
             => Machine f var cat ctx -> m (cat Void)
runUnbounded = tailRecM step


evalUnbounded :: forall f var cat ctx m .
                 MonadRec m
              => Context var (Closure f var cat ctx) ctx
              => Recursive (f (LambdaF var cat)) (LambdaF var cat)
              => Evaluate f var cat m
              => MachineFault f var cat ctx m
              => Closure f var cat ctx -> m (cat Void)
evalUnbounded c = runUnbounded (c :< Nothing)

