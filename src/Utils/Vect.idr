module Utils.Vect

import Data.Vect
import Data.Vect.Quantifiers

%default total

public export
appendNilRightNeutral : {n : Nat} -> (xs : Vect n a) -> (xs ++ [] = (rewrite plusZeroRightNeutral n in xs))
appendNilRightNeutral [] = Refl
appendNilRightNeutral {n = S len} (x :: xs) = rewrite appendNilRightNeutral xs in rewrite plusZeroRightNeutral len in Refl

public export
appendAssociative : {n : Nat} -> (left : Vect n a) -> {m : Nat} -> (center : Vect m a) -> {k : Nat} -> (right : Vect k a) -> left ++ (center ++ right) = (rewrite plusAssociative n m k in (left ++ center) ++ right)
appendAssociative [] center right = Refl
appendAssociative {n = S len} (x :: xs) center right = rewrite appendAssociative xs center right in rewrite plusAssociative len m k in Refl
