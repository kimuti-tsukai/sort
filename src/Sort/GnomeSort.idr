module Sort.GnomeSort

import Data.Vect
import Data.Vect.Quantifiers
import Control.Order
import Control.Relation

import Sort
import Proofs.Permutation
import Proofs.Sorted

%default total

gnomeSort : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => SortAlgorithm a rel
gnomeSort rel [] = ([] ** (PermNil, Nil))
gnomeSort rel [x] = ([x] ** (permRefl, Cons x Nil Nil))
gnomeSort rel (x :: y :: xs) =
  let (y' :: xs' ** (perm, sorted@(Cons _ yLTxs' _))) = gnomeSort rel (y :: xs)
  in case order x y' of
    Left xLTEy' => (x :: y' :: xs' ** (PermSkip x perm, (consWithHeadOrder x xLTEy' sorted)))
    Right y'LTEx =>
      let
        (x' :: xs'' ** (perm', sorted')) = gnomeSort rel (x :: xs')
        perm''' = PermTrans (PermSkip x perm) (PermTrans (PermSwap x y' xs') (PermSkip y' perm'))
      in (y' :: x' :: xs'' ** (perm''', Cons y' (permAll perm' (y'LTEx :: yLTxs')) sorted'))
