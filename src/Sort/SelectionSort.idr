module Sort.SelectionSort

import Data.Vect
import Data.Vect.Quantifiers
import Data.Vect.Elem

import Proofs.Sorted
import Proofs.Permutation
import Utils.Relation

%default total

getMin : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => (xs : Vect (S n) a) -> (x : a ** (Elem x xs, All (rel x) xs))
getMin rel [x] = (x ** (Here, stronglyConnexReflexive rel :: Nil))
getMin rel (x :: y :: xs) =
  let (min ** (elem, minLTEyxs)) = getMin rel (y :: xs)
  in case order x min of
    Left xLTEmin => (x ** (Here, stronglyConnexReflexive rel :: extendTrans xLTEmin minLTEyxs))
    Right minLTEx => (min ** (There elem, minLTEx :: minLTEyxs))

updateElem : (xs : Vect n a) -> {before : a} -> Elem before xs -> (after : a) -> (ys : Vect n a ** Permutation (after :: xs) (before :: ys))
updateElem (x :: xs) Here after = (after :: xs ** (PermSwap after x xs))
updateElem (x :: xs) (There elem) after =
  let (xs' ** perm) = updateElem xs elem after in (x :: xs' ** PermTrans (PermSwap after x xs) (PermTrans (PermSkip x perm) (PermSwap x before xs')))

public export
selectionSort : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => (xs : Vect n a) -> (ys : Vect n a ** (Permutation xs ys, Sorted rel ys))
selectionSort rel [] = ([] ** (PermNil, Nil))
selectionSort rel (x :: xs) with (getMin rel (x :: xs))
  _ | (_ ** (Here, _ :: xLTExs)) =
    let (xs' ** (perm, sorted)) = selectionSort rel xs in (x :: xs' ** (PermSkip x perm, Cons x (permAll perm xLTExs) sorted))
  _ | (min ** (There elem, (minLTEx :: minLTExs))) =
    let
      (xs' ** perm) = updateElem xs elem x
      (xs'' ** (perm', sorted)) = selectionSort rel xs'
      (_ :: minLTExs') = permAll perm (minLTEx :: minLTExs)
    in (min :: xs'' ** (PermTrans perm (PermSkip min perm'), Cons min (permAll perm' minLTExs') sorted))
