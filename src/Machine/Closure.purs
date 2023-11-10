module Machine.Closure where

import Data.Tuple.Nested (type (/\), (/\))
import Language.Lambda.Calculus (LambdaF)

newtype Closure f var cat ctx = Closure ((f (LambdaF var cat)) /\ ctx)

closure :: forall f var cat ctx. f (LambdaF var cat) -> ctx -> Closure f var cat ctx
closure term ctx = Closure (term /\ ctx)

