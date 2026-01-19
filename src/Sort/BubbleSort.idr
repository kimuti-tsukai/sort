module Sort.BubbleSort

import Data.Vect
import Data.Vect.Quantifiers
import Control.Order
import Control.Relation

import Proofs.Permutation
import Proofs.Sorted
import Utils.Relation

bubblePass :
  (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel)
  => (xs : Vect (S n) a)
  -> Either (x : a ** v : Vect n a ** (Permutation xs (x :: v), All (rel x) v)) (Sorted rel xs)
bubblePass rel [x] = Right (Cons x Nil Nil)
bubblePass rel @{(sc, _)} (x :: y :: xs) with (bubblePass rel (y :: xs))
  _ | (Right sortedYXs@(Cons y yLTys sortedYs)) =
    case order @{sc} x y of
      Left xLTEy => Right (consWithHeadOrder x xLTEy sortedYXs)
      Right yLTEx => Left (y ** x :: xs ** (PermSwap x y xs, yLTEx :: yLTys))
  _ | (Left (y' ** xs' ** (perm, yLTEx))) =
    case order @{sc} x y' of
      Left xLTEy' => Left (x ** y' :: xs' ** (PermSkip x perm, xLTEy' :: extendTrans xLTEy' yLTEx))
      Right y'LTEx => Left (y' ** x :: xs' ** (PermTrans (PermSkip x perm) (PermSwap x y' xs'), y'LTEx :: yLTEx))

bubbleSort : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
bubbleSort rel [] = ([] ** (PermNil, Nil))
bubbleSort rel (x :: xs) with (bubblePass rel (x :: xs))
  _ | (Right sortedXXs) = (x :: xs ** (permRefl, sortedXXs))
  _ | (Left (y ** ys ** (perm, yLTEys))) =
    let (ys' ** (permYsYs', sortedYs')) = bubbleSort rel ys in
      (y :: ys' ** (PermTrans perm (PermSkip y permYsYs'), Cons y (permAll permYsYs' yLTEys) sortedYs'))
