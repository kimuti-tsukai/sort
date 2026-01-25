module Sort

import Data.Vect
import Control.Order
import Control.Relation

import Proofs.Permutation
import Proofs.Sorted

%default total

public export
SortAlgorithm : (a : Type) -> (rel : a -> a -> Type) -> Type
SortAlgorithm a rel = {n : Nat} -> (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
