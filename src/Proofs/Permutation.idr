module Proofs.Permutation

import Data.Vect
import Data.Vect.Quantifiers
import Data.Vect.Elem

import Utils.Vect

%default total

public export
data Permutation : Vect n a -> Vect n a -> Type where
  PermNil : Permutation [] []
  PermSkip : (x : a) -> Permutation xs ys -> Permutation (x :: xs) (x :: ys)
  PermSwap : (x : a) -> (y : a) -> (xs : Vect n a) -> Permutation (x :: y :: xs) (y :: x :: xs)
  PermTrans : {ys : Vect n a} -> (p : Permutation xs ys) -> (q : Permutation ys zs) -> Permutation xs zs

public export
permRefl : {xs : Vect n a} -> Permutation xs xs
permRefl {xs = []} = PermNil
permRefl {xs = (x :: ys)} = PermSkip x permRefl

public export
permSym : {xs : Vect n a} -> {ys : Vect n a} -> Permutation xs ys -> Permutation ys xs
permSym PermNil = PermNil
permSym (PermSkip x pr) = PermSkip x (permSym pr)
permSym (PermSwap x y xs) = PermSwap y x xs
permSym (PermTrans p1 p2) = PermTrans (permSym p2) (permSym p1)

public export
permAll : Permutation xs ys -> All p xs -> All p ys
permAll PermNil allXs = allXs
permAll (PermSkip x pr) (px :: pxs) = px :: permAll pr pxs
permAll (PermSwap x y xs) (px :: py :: p_xs) = py :: px :: p_xs
permAll (PermTrans p1 p2) allXs = permAll p2 (permAll p1 allXs)

public export
permAppendLeft : Permutation v1 v2 -> (v3 : Vect m a) -> Permutation (v1 ++ v3) (v2 ++ v3)
permAppendLeft PermNil v3 = permRefl
permAppendLeft (PermSkip x pr) v3 = PermSkip x (permAppendLeft pr v3)
permAppendLeft (PermSwap x y xs) v3 = PermSwap x y (xs ++ v3)
permAppendLeft (PermTrans p1 p2) v3 =
  PermTrans (permAppendLeft p1 v3) (permAppendLeft p2 v3)

public export
permAppendRight : (v1 : Vect n a) -> Permutation v3 v4 -> Permutation (v1 ++ v3) (v1 ++ v4)
permAppendRight [] pr = pr
permAppendRight (x :: xs) pr = PermSkip x (permAppendRight xs pr)

public export
permAppend : {v2 : Vect m a} -> {v3 : Vect n a} -> Permutation v1 v2 -> Permutation v3 v4 -> Permutation (v1 ++ v3) (v2 ++ v4)
permAppend p12 p34 =
  PermTrans (permAppendLeft p12 v3) (permAppendRight v2 p34)

public export
permMoveHeadToMiddle :
  (x : a)
  -> {n : Nat} -> (v1 : Vect n a)
  -> {m : Nat} -> (v2 : Vect m a)
  -> Permutation (x :: v1 ++ v2) (rewrite plusSuccRightSucc n m in (v1 ++ x :: v2))
permMoveHeadToMiddle x [] v2 = permRefl
permMoveHeadToMiddle x {n = S len} (y :: ys) {m} v2 =
  rewrite sym (plusSuccRightSucc len m) in PermTrans (PermSwap x y (ys ++ v2)) (PermSkip y (permMoveHeadToMiddle x ys v2))

public export
permAppendCommutative : {n : Nat} ->  (v1 : Vect n a) -> {m : Nat} -> (v2 : Vect m a) -> Permutation (v1 ++ v2) (rewrite plusCommutative n m in (v2 ++ v1))
permAppendCommutative [] v2 = rewrite appendNilRightNeutral v2 in permRefl
permAppendCommutative {n = S len} (x :: xs) v2 =
  PermTrans (PermSkip x (permAppendCommutative xs v2)) (rewrite plusCommutative len m in permMoveHeadToMiddle x v2 xs)

public export
permElem : Permutation v1 v2 -> Elem x v1 -> Elem x v2
permElem (PermSkip x p) Here = Here
permElem (PermSkip x p) (There y) = There (permElem p y)
permElem (PermSwap x y xs) Here = There Here
permElem (PermSwap x y xs) (There Here) = Here
permElem (PermSwap x y xs) (There (There e)) = There (There (e))
permElem (PermTrans p1 p2) e = permElem p2 (permElem p1 e)

public export
replace : Fin n -> (x : a) -> (xs : Vect n a) -> (y : a ** ys : Vect n a ** Permutation (x :: xs) (y :: ys))
replace 0 x (y :: xs) = (y ** x :: xs ** PermSwap x y xs)
replace (FS n) x (x' :: y :: xs) =
  let (y' ** ys ** perm) = replace n x (y :: xs)
  in (y' ** x' :: ys ** PermTrans (PermSwap x x' (y :: xs)) (PermTrans (PermSkip x' perm) (PermSwap x' y' ys)))

public export
swap : Fin n -> Fin n -> (xs : Vect n a) -> (ys : Vect n a ** Permutation xs ys)
swap FZ FZ xs = (xs ** permRefl)
swap FZ (FS n) (x :: xs) = let (y ** ys ** perm) = replace n x xs in (y :: ys ** perm)
swap (FS n) FZ (x :: xs) = let (y ** ys ** perm) = replace n x xs in (y :: ys ** perm)
swap (FS n) (FS m) (x :: xs) = let (ys ** perm) = swap n m xs in (x :: ys ** PermSkip x perm)

public export
replaceElem : (x' : a) -> (xs : Vect n a) -> {x : a} -> Elem x xs -> (ys : Vect n a ** (Elem x' ys, Permutation (x' :: xs) (x :: ys)))
replaceElem x' (x :: xs) Here = (x' :: xs ** (Here, PermSwap x' x xs))
replaceElem x' (y :: z :: xs) (There e) =
  let (ys ** (elem, perm)) = replaceElem x' (z :: xs) e
  in (y :: ys ** (There elem, PermTrans (PermSwap x' y (z :: xs)) (PermTrans (PermSkip y perm) (PermSwap y x ys))))
