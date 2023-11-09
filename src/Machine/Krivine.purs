module Machine.Krivine where

-- For a description of Krivine Machines see this article
-- https://www.pls-lab.org/en/Krivine_machine

import Prelude

import Control.Comonad (extend)
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Comonad.Store (class ComonadStore, peek, pos)
import Control.Monad.Rec.Class (Step(..))
import Data.Maybe (Maybe(..), maybe)
import Language.Lambda.Calculus (LambdaF(..))
import Matryoshka.Class.Recursive (class Recursive, project)

data Closure f var cat ctx =
  Closure (f (LambdaF var cat)) (ctx (Maybe (Closure f var cat ctx)))

type Machine f var cat ctx = Cofree Maybe (Closure f var cat ctx)

data Halt var halt =
    ContextFault var
  | StackFault
  | Halt halt

class Morph f var cat ctx halt m where
  morph :: cat (f (LambdaF var cat))
        -> ctx (Maybe (Closure f var cat ctx))
        -> Maybe (Machine f var cat ctx)
        -> m (Step (Machine f var cat ctx) (Halt var halt))

step :: forall f var cat ctx halt m .
        Monad m
     => Eq var
     => ComonadStore var ctx
     => Recursive (f (LambdaF var cat)) (LambdaF var cat)
     => Morph f var cat ctx halt m
     => Machine f var cat ctx -> m (Step (Machine f var cat ctx) (Halt var halt))
step machine = do
  let Closure term context = head machine
  case project term of
    Abs var body ->
      case tail machine of
          Nothing -> pure $ Done StackFault
          Just stack -> do
             let varBind ctx = if pos ctx == var
                                 then Just (head stack)
                                 else peek (pos ctx) ctx
             pure $ Loop $ (Closure body (extend varBind context)) :< tail stack 
    App f g ->
      pure $ Loop $ (Closure f context) :< Just ((Closure g context) :< tail machine)
    Var var -> do
      let continue closure = closure :< tail machine
      pure $ maybe (Done $ ContextFault var) (Loop <<< continue) (peek var context)
    Cat c -> morph c context (tail machine)

