module Language.Kernel.Library where


import Data.FoldableWithIndex (foldrWithIndex)
import Data.Homogeneous (class HomogeneousRowLabels, class Keys, class ToHomogeneousRow, keysImpl)
import Data.Homogeneous.Record (Homogeneous, fromHomogeneous, homogeneous)
import Data.List (List(..), (:))
import Data.Tuple.Nested (type (/\), (/\))
import Prim.Row (class Union)
import Prim.RowList (class RowToList)
import Record (union)
import Type.Proxy (Proxy(..))

type Kernel term = List (String /\ term)

compileKernel :: forall ra names term .
                 ToHomogeneousRow names term ra
              => KernelLibrary names term -> Kernel term
compileKernel h = foldrWithIndex (\s n l -> (s /\ n):l) Nil h

kernelStrings :: forall names list . RowToList names list => Keys list => Proxy names -> List String
kernelStrings _ = keysImpl (Proxy :: Proxy list)
  
type KernelLibrary names term = Homogeneous names term

kernelLibraryUnion :: forall l rl r rr u ru term .
                Union rl rr ru
             => ToHomogeneousRow l term rl
             => ToHomogeneousRow r term rr
             => HomogeneousRowLabels ru term u
             => KernelLibrary l term
             -> KernelLibrary r term
             -> KernelLibrary u term
kernelLibraryUnion l r =
  let z :: Record ru
      z = union (fromHomogeneous l) (fromHomogeneous r)
  in homogeneous z
 
