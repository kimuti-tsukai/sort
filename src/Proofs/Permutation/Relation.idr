module Proofs.Permutation.Relation

import Proofs.Permutation

import Data.Vect
import Control.Relation

public export
Reflexive (Vect n a) (Permutation) where
  reflexive = permRefl

public export
Symmetric (Vect n a) (Permutation) where
  symmetric = permSym

public export
Transitive (Vect n a) (Permutation) where
  transitive = PermTrans
