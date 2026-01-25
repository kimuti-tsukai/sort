module Sort.InsertionSort

import Data.Vect
import Data.Vect.Quantifiers

import Sort
import Proofs.Permutation
import Proofs.Sorted
import Utils.Relation

%default total

public export
insertInOrder :
  (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel)
  => (x : a)
  -> (xs : Vect n a) -> Sorted rel xs
  -> (ys : Vect (S n) a ** (Permutation (x :: xs) ys, Sorted rel ys))
insertInOrder rel x [] Nil = ([x] ** (permRefl, (Cons x [] Nil)))
insertInOrder rel @{(sc, _)} x (y :: ys) sorted with (order @{sc} x y)
  insertInOrder rel x (y :: ys) sorted@(Cons _ allRelYs sorted') | (Left xLTy) =
    (x :: y :: ys ** (PermSkip x permRefl, Cons x (xLTy :: (extendTrans xLTy allRelYs)) sorted))
  insertInOrder rel x (y :: ys) (Cons _ yLTAll sorted) | (Right yLTx) =
    let
      (v ** (perm, sorted')) = insertInOrder rel x ys sorted
      perm' = PermTrans (PermSwap x y ys) (PermSkip y perm)
      yLTxAll = yLTx :: yLTAll
      yLTv = permAll perm yLTxAll
      sorted'' = Cons y yLTv sorted'
    in (y :: v ** (perm', sorted''))

export
insertionSort : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
insertionSort rel [] = ([] ** (PermNil, Nil))
insertionSort rel (x :: xs) =
  let
    (v ** (perm, sorted)) = insertionSort rel xs
    (inserted ** (perm', sorted')) = insertInOrder rel x v sorted
  in (inserted ** (PermTrans (PermSkip x perm) perm', sorted'))

export
insertionSort' : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => SortAlgorithm a rel
insertionSort' rel xs = insertionSort rel xs
