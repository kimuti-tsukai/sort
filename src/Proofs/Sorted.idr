module Proofs.Sorted

import Data.Vect
import Data.Vect.Quantifiers

import Utils.Vect
import Utils.Relation

%default total

public export
data Sorted : (rel : a -> a -> Type) -> Vect n a -> Type where
  Nil : Sorted rel []
  Cons : (x : a) -> {xs : Vect n a} -> All (rel x) xs -> Sorted rel xs -> Sorted rel (x :: xs)

public export
sortedSingleton : {rel : a -> a -> Type} -> (x : a) -> Sorted rel [x]
sortedSingleton x = Cons x Nil Nil

public export
concatSorted :
  {rel : a -> a -> Type} -> Transitive a rel
  => {v1 : Vect n a} -> Sorted rel v1
  -> {v2 : Vect m a} -> Sorted rel v2
  -> (mid : a)
  -> All (\v => rel v mid) v1 -> All (rel mid) v2
  -> Sorted rel (v1 ++ v2)
concatSorted Nil sorted2 mid allLTE allGTE = sorted2
concatSorted (Cons x {xs} allRel sortedXs) sorted2 mid (relX :: allLTE) allGTE =
  let tail = concatSorted sortedXs sorted2 mid allLTE allGTE
  in Cons x (allRel ++ extendTrans relX allGTE) tail

public export
concatSortedWithMid :
  {rel : a -> a -> Type} -> Transitive a rel
  => {v1 : Vect n a} -> Sorted rel v1
  -> {v2 : Vect m a} -> Sorted rel v2
  -> (mid : a)
  -> All (\v => rel v mid) v1 -> All (rel mid) v2
  -> Sorted rel (v1 ++ mid :: v2)
concatSortedWithMid Nil sorted2 mid allLTE allGTE = Cons mid allGTE sorted2
concatSortedWithMid (Cons x {xs} xLTExs sortedXs) sortedYs mid (xLTEmid :: xsLTEmid) midLTEys =
  let tail = concatSortedWithMid sortedXs sortedYs mid xsLTEmid midLTEys
  in Cons x (xLTExs ++ xLTEmid :: extendTrans xLTEmid midLTEys) tail

public export
consWithHeadOrder : {rel : a -> a -> Type} -> Transitive a rel => (x : a) -> rel x y -> Sorted rel (y :: xs) -> Sorted rel (x :: y :: xs)
consWithHeadOrder x xLTy (Cons y yLTys sortedYs) = Cons x (xLTy :: extendTrans xLTy yLTys) (Cons y yLTys sortedYs)
