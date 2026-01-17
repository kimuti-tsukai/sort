module Sort.QuickSort

import Data.Vect
import Data.Vect.Quantifiers
import Control.Order
import Control.Relation
import Control.WellFounded

import Proofs.Permutation
import Proofs.Sorted
import Sort.InsertionSort

%default total

partitionWithProof :
  {s : a -> Type} -> {t : a -> Type}
  -> (p : (v : a) -> Either (s v) (t v))
  -> (xs : Vect len a)
  -> (n : Nat ** m : Nat ** prf : len = n + m ** v1 : Vect n a ** v2 : Vect m a ** (All s v1, All t v2, Permutation xs (rewrite prf in v1 ++ v2)))
partitionWithProof p [] = (0 ** 0 ** Refl ** [] ** [] ** ([], [], PermNil))
partitionWithProof p (x :: xs) with (p x)
  _ | Left l =
    let (n ** m ** prf ** v1 ** v2 ** (prf1, prf2, perm)) = partitionWithProof p xs
    in (S n ** m ** cong S prf ** x :: v1 ** v2 ** (l :: prf1, prf2, rewrite sym prf in PermSkip x perm))
  _ | Right r =
    let (n ** m ** prf ** v1 ** v2 ** (prf1, prf2, perm)) = partitionWithProof p xs
    in (n ** S m ** rewrite sym (plusSuccRightSucc n m) in cong S prf ** v1 ** x :: v2 ** (prf1, r :: prf2, PermTrans (PermSkip x perm) (rewrite prf in permMoveHeadToMiddle x v1 v2)))

quickSortInner : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> Accessible LT n -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
quickSortInner _ [] _ = ([] ** (PermNil, Nil))
quickSortInner rel @{(sc, _)} (x :: xs) (Access acc) =
  let
    (nl ** nr ** prf ** le ** gt ** (allLTE, allGT, perm)) = partitionWithProof (\v => order @{sc} v x) xs
    nlLTn = rewrite prf in LTESucc $ lteAddRight nl
    nrLTn = rewrite prf in rewrite plusCommutative nl nr in LTESucc $ lteAddRight nr
    (leSorted ** (permLE, sortedLE)) = quickSortInner rel le (acc nl nlLTn)
    (gtSorted ** (permGT, sortedGT)) = quickSortInner rel gt (acc nr nrLTn)
    proof' = trans (cong S prf) (plusSuccRightSucc nl nr)
    sorted = concatSortedWithMid sortedLE sortedGT x (permAll permLE allLTE) (permAll permGT allGT)
    permRight = PermSkip x permGT
    permResult = permAppend permLE permRight
    permLeft = PermTrans (PermSkip x perm) (rewrite prf in permMoveHeadToMiddle x le gt)
    permprf = PermTrans (rewrite sym proof' in permLeft) permResult
  in rewrite proof' in (leSorted ++ x :: gtSorted ** (permprf, sorted))

export
quickSort : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
quickSort rel xs = quickSortInner rel xs (wellFounded n)

threshold : Nat
threshold = 32

quickSortHybridInner : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> Accessible LT n -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
quickSortHybridInner _ [] _ = ([] ** (PermNil, Nil))
quickSortHybridInner rel @{(sc, _)} (x :: xs) (Access acc) =
  let
    (nl ** nr ** prf ** le ** gt ** (allLTE, allGT, perm)) = partitionWithProof (\v => order @{sc} v x) xs
    nlLTn = rewrite prf in LTESucc $ lteAddRight nl
    nrLTn = rewrite prf in rewrite plusCommutative nl nr in LTESucc $ lteAddRight nr
    (leSorted ** (permLE, sortedLE)) = if nl >= threshold then quickSortInner rel le (acc nl nlLTn) else insertionSort rel le
    (gtSorted ** (permGT, sortedGT)) = if nr >= threshold then quickSortInner rel gt (acc nr nrLTn) else insertionSort rel gt
    proof' = trans (cong S prf) (plusSuccRightSucc nl nr)
    sorted = concatSortedWithMid sortedLE sortedGT x (permAll permLE allLTE) (permAll permGT allGT)
    permRight = PermSkip x permGT
    permResult = permAppend permLE permRight
    permLeft = PermTrans (PermSkip x perm) (rewrite prf in permMoveHeadToMiddle x le gt)
    permprf = PermTrans (rewrite sym proof' in permLeft) permResult
  in rewrite proof' in (leSorted ++ x :: gtSorted ** (permprf, sorted))

export
quickSortHybrid : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
quickSortHybrid rel xs = quickSortHybridInner rel xs (wellFounded n)
