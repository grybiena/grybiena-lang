module Language.Module where


import Data.FoldableWithIndex (foldrWithIndex)
import Data.Homogeneous (class HomogeneousRowLabels, class Keys, class ToHomogeneousRow, keysImpl)
import Data.Homogeneous.Record (Homogeneous, fromHomogeneous, homogeneous)
import Data.List (List(..), (:))
import Data.Tuple.Nested (type (/\), (/\))
import Prim.Row (class Union)
import Prim.RowList (class RowToList)
import Record (union)
import Type.Proxy (Proxy(..))

type Listing term = List (String /\ term)

moduleListing :: forall ra names term .
                 ToHomogeneousRow names term ra
              => Module names term -> Listing term
moduleListing h = foldrWithIndex (\s n l -> (s /\ n):l) Nil h

listingBinds :: forall names list . RowToList names list => Keys list => Proxy names -> List String
listingBinds _ = keysImpl (Proxy :: Proxy list)
  
type Module names term = Homogeneous names term

moduleUnion :: forall l rl r rr u ru term .
                Union rl rr ru
             => ToHomogeneousRow l term rl
             => ToHomogeneousRow r term rr
             => HomogeneousRowLabels ru term u
             => Module l term
             -> Module r term
             -> Module u term
moduleUnion l r =
  let z :: Record ru
      z = union (fromHomogeneous l) (fromHomogeneous r)
  in homogeneous z
 
