module Sort.MergeSort

import Data.Fin
import Data.Fin.Extra
import Data.Vect
import Data.Vect.Quantifiers
import Control.Order
import Control.Relation
import Control.WellFounded

import Proofs.Permutation
import Proofs.Sorted
import Utils.Vect
import Utils.Relation
import Sort.InsertionSort

%default total

split : {n : Nat} -> (xs : Vect n a) -> (nl, nr : Nat) -> (prf : n = nl + nr) -> (v1 : Vect nl a ** v2 : Vect nr a ** xs = (rewrite prf in v1 ++ v2))
split xs 0 nr prf = ([] ** (rewrite plusZeroLeftNeutral nr in rewrite sym prf in xs) ** Refl)
split (x :: xs) (S l) nr prf =
  let
    lenprf' = cong pred prf
    (v1 ** v2 ** prf') = split xs l nr lenprf'
  in (x :: v1 ** v2 ** rewrite sym lenprf' in cong (x ::) prf')

divInTwo : (n : Nat) -> LTE 2 n -> (nl : Nat ** nr : Nat ** (n = nl + nr, LT nl n, LT nr n))
divInTwo n lte2n with (divMod n 2)
  _ | (Fraction _ _ q 0 prf) =
    let eqPrf = sym $ rewrite sym prf in rewrite plusZeroRightNeutral (mult q 2) in rewrite multCommutative q 2 in rewrite plusZeroRightNeutral q in Refl
    in (q ** q ** (eqPrf, lemma lte2n eqPrf, lemma lte2n eqPrf))
  where
    lemma : {n, q : Nat} -> LTE 2 n -> (n = q + q) -> LT q n
    lemma {q = 0} lte2n prf = absurd (replace prf lte2n)
    lemma {q = S q'} lte2n prf = rewrite prf in rewrite sym $ plusSuccRightSucc q' q' in lteAddRight (S (S q'))
  _ | (Fraction _ _ q 1 prf) =
    let
      eqPrf = sym $ rewrite sym prf in rewrite multCommutative q 2 in rewrite plusZeroRightNeutral q in rewrite plusCommutative (q + q) 1 in Refl
      sqLTn = lemma lte2n eqPrf
      qLTn = lteSuccLeft sqLTn
    in (S q ** q ** (eqPrf, sqLTn, qLTn))
    where
      lemma : {n, q : Nat} -> LTE 2 n -> (n = S (q + q)) -> LT (S q) n
      lemma {q = 0} lte2n prf = absurd (replace prf lte2n)
      lemma {q = S q'} lte2n prf = rewrite prf in rewrite sym $ plusSuccRightSucc q' q' in lteAddRight (S (S (S q')))

public export
mergeSorted :
  (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel)
  => {left : Nat} -> (xs : Vect left a) -> Sorted rel xs
  -> {right : Nat} -> (ys : Vect right a) -> Sorted rel ys
  -> (v : Vect (left + right) a ** (Permutation (xs ++ ys) v, Sorted rel v))
mergeSorted rel [] _ ys sortedYs = (ys ** (permRefl, sortedYs))
mergeSorted rel xs sortedXs [] _ = rewrite plusZeroRightNeutral left in rewrite appendNilRightNeutral xs in (xs ** (permRefl, sortedXs))
mergeSorted rel @{(sc, _)} {left = S ll} (x :: xs) sortedXXs@(Cons _ xLTxs sortedXs) {right = S lr} (y :: ys) sortedYYs@(Cons _ yLTys sortedYs) with (order @{sc} x y)
  _ | Left xLTy =
    let
      (v ** (permV, sortedV)) = mergeSorted rel xs sortedXs (y :: ys) sortedYYs
      xLTys = extendTrans xLTy yLTys
      xLTxsXYs = xLTxs ++ xLTy :: xLTys
      xLTv = permAll permV xLTxsXYs
    in (x :: v ** (PermSkip x permV, Cons x xLTv sortedV))
  _ | Right yLTx =
    let
      (v ** (permV, sortedV)) = mergeSorted rel (x :: xs) sortedXXs ys sortedYs
      perm' = permSym $ PermTrans (PermSwap y x (xs ++ ys)) (PermSkip x (permMoveHeadToMiddle y xs ys))
      perm'' = PermTrans perm' (PermSkip y permV)
      yLTxs = extendTrans yLTx xLTxs
      yLTxXsYs = yLTx :: yLTxs ++ yLTys
      yLTv = permAll permV yLTxXsYs
    in rewrite sym $ plusSuccRightSucc ll lr in (y :: v ** (perm'', Cons y yLTv sortedV))

mergeSortInner : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> Accessible LT n -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
mergeSortInner _ [] _ = ([] ** (PermNil, Nil))
mergeSortInner _ [x] _ = ([x] ** (permRefl, Cons x Nil Nil))
mergeSortInner rel {n = S (S len)} xs (Access acc) =
  let
    (nl ** nr ** (eqPrf, nlLTn, nrLTn)) = divInTwo (S (S len)) %search
    (left ** right ** appendPrf) = split xs nl nr eqPrf
    (vl ** (permLeftVl, sortedVl)) = mergeSortInner rel left (acc nl nlLTn)
    (vr ** (permRightVr, sortedVr)) = mergeSortInner rel right (acc nr nrLTn)
    (v ** (permV, sortedV)) = mergeSorted rel vl sortedVl vr sortedVr
    perm' = PermTrans (permAppend permLeftVl permRightVr) permV
  in rewrite eqPrf in (v ** (rewrite appendPrf in perm', sortedV))

export
mergeSort : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
mergeSort rel xs = mergeSortInner rel xs (wellFounded n)

threshold : Nat
threshold = 32

mergeSortHybridInner : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> Accessible LT n -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
mergeSortHybridInner _ [] _ = ([] ** (PermNil, Nil))
mergeSortHybridInner _ [x] _ = ([x] ** (permRefl, Cons x Nil Nil))
mergeSortHybridInner rel {n = S (S len)} xs (Access acc) =
  let
    (nl ** nr ** (eqPrf, nlLTn, nrLTn)) = divInTwo (S (S len)) %search
    (left ** right ** appendPrf) = split xs nl nr eqPrf
    (vl ** (permLeftVl, sortedVl)) = if nl >= threshold then mergeSortHybridInner rel left (acc nl nlLTn) else insertionSort rel left
    (vr ** (permRightVr, sortedVr)) = if nr >= threshold then mergeSortHybridInner rel right (acc nr nrLTn) else insertionSort rel right
    (v ** (permV, sortedV)) = mergeSorted rel vl sortedVl vr sortedVr
    perm' = PermTrans (permAppend permLeftVl permRightVr) permV
  in rewrite eqPrf in (v ** (rewrite appendPrf in perm', sortedV))

export
mergeSortHybrid : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
mergeSortHybrid rel xs = mergeSortHybridInner rel xs (wellFounded n)
