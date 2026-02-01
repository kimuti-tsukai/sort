module Proofs.Permutation.Properties

import Data.Vect
import Data.Vect.Elem
import Data.Vect.Quantifiers
import Decidable.Equality
import Control.Order
import Control.Relation

import Proofs.Sorted
import Proofs.Permutation
import Sort
import Sort.MergeSort
import Utils.Relation

%default total

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

sortedPermHeadIsEq : {rel : a -> a -> Type} -> Antisymmetric a rel => {x, y : a} -> {xs, ys : Vect n a} -> All (rel x) (x :: xs) -> All (rel y) (y :: ys) -> Permutation (x :: xs) (y :: ys) -> x = y
sortedPermHeadIsEq (reflX :: xLTExs) (reflY :: yLTEys) p =
  let
    (xLTEy :: _) = permAll p (reflX :: xLTExs)
    (yLTEx :: _) = permAll (permSym p) (reflY :: yLTEys)
  in antisymmetric xLTEy yLTEx

permSortedIsEq : (xsSorted : Vect n a) -> (ysSorted : Vect n a) -> Permutation xsSorted ysSorted -> {rel : a -> a -> Type} -> (Antisymmetric a rel, Reflexive a rel) => Sorted rel xsSorted -> Sorted rel ysSorted -> xsSorted = ysSorted
permSortedIsEq [] [] _ _ _  = Refl
permSortedIsEq (sx :: sxs) (sy :: sys) perm (Cons sx sxLTEsxs sortedSxs) (Cons sy syLTEsys sortedSys) =
  let sxEQsy = sortedPermHeadIsEq (reflexive :: sxLTEsxs) (reflexive :: syLTEsys) perm in
  let permSxsSys = permSkipPerm (replace {p = \sx => Permutation (sx :: sxs) (sy :: sys)} sxEQsy perm) in
  rewrite sxEQsy in rewrite permSortedIsEq sxs sys permSxsSys sortedSxs sortedSys in Refl

decPermutationBySort : (rel : a -> a -> Type) -> (DecEq a, StronglyConnex a rel, Transitive a rel, Antisymmetric a rel) => {n : Nat} -> (xs : Vect n a) -> (ys : Vect n a) -> Dec (Permutation xs ys)
decPermutationBySort rel @{(de, sc, ts, at)} xs ys with (mergeSortHybrid rel xs, mergeSortHybrid rel ys)
  _ | ((xsSorted ** (perm1, sorted1)), (ysSorted ** (perm2, sorted2))) with (decEq xsSorted ysSorted)
    _ | (Yes eq) = Yes (PermTrans perm1 (rewrite eq in permSym perm2))
    _ | (No neq) = No (\p => neq (permSortedIsEq xsSorted ysSorted (PermTrans (permSym perm1) (PermTrans p perm2)) @{(at, StronglyConnexReflexive)} sorted1 sorted2))
