module Proofs.Permutation.Properties

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

import Proofs.Permutation
import Sort.MergeSort

notElem : (x = y -> Void) -> (Elem x xs -> Void) -> Elem x (y :: xs) -> Void
notElem xEQy _ Here = xEQy Refl
notElem _ notElemHere (There later) = notElemHere later

searchAndRemove : DecEq a => (x : a) -> (xs : Vect (S n) a) -> Either (ys : Vect n a ** (Permutation xs (x :: ys))) (Not (Elem x xs))
searchAndRemove x [y] with (decEq x y)
  _ | (Yes xEQy) = Left ([] ** rewrite xEQy in permRefl)
  _ | (No xNotEQy) = Right (\Here => xNotEQy Refl)
searchAndRemove x (y :: z :: rest) with (decEq x y)
  _ | (Yes xEQy) = Left (z :: rest ** rewrite xEQy in permRefl)
  _ | (No xNotEQy) with (searchAndRemove x (z :: rest))
    _ | Left (ys ** perm) = Left (y :: ys ** (PermTrans (PermSkip y perm) (PermSwap y x ys)))
    _ | Right xNotElem = Right (notElem xNotEQy xNotElem)

public export
decPermutation : (DecEq a) => (xs : Vect n a) -> (ys : Vect n a) -> Dec (Permutation xs ys)
decPermutation [] [] = Yes PermNil
decPermutation (x :: xs) ys with (searchAndRemove x ys)
  _ | Left (ys' ** perm) with (decPermutation xs ys')
    _ | Yes perm' = Yes (PermTrans (PermSkip x perm') (permSym perm))
    _ | No permNot = No notPerm
      where
        notPerm : Permutation (x :: xs) ys -> Void
        notPerm p = permNot (permSkipPerm (PermTrans p perm))
  _ | Right xNotElem = No notPerm
      where
        notPerm : Permutation (x :: xs) ys -> Void
        notPerm p = xNotElem (permElem p Here)
