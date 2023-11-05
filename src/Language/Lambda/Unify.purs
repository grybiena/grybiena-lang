module Language.Lambda.Unify where

import Prelude

import Data.Functor.Mu (Mu)
import Data.Tuple.Nested ((/\))
import Language.Lambda.Calculus (LambdaF(..))
import Matryoshka.Class.Recursive (class Recursive, project)


--instance Monad m => Unification String TT (UnifyT m) where 
--  fresh = do
--    nextVar <- gets (\(UnificationState st) -> st.nextVar)
--    let t = In (Var ("t" <> show nextVar))
--    modify_ (\(UnificationState st) -> UnificationState st { nextVar = st.nextVar + 1 })
--    pure t
--  applyCurrentSubstitution = pure --TODO
--  replaceVarWithFresh _ = pure --TODO
--  substitute s t = do
--     modify_ (\(UnificationState st) -> UnificationState st { currentSubstitution = Map.insert s t st.currentSubstitution })
--  unificationError t = throwError <<< UnificationError t
--  skolemize _ = pure
--



