module Utils.Relation

import Data.Nat
import Data.Vect
import Data.Vect.Quantifiers
import Control.Order
import Control.Relation

%default total

public export
extendTrans : Transitive a rel => {x : a} -> {y : a} -> (xLTy : rel x y) -> {ys : Vect k a} -> All (rel y) ys -> All (rel x) ys
extendTrans xLTy [] = []
extendTrans xLTy (pr :: prs) = transitive xLTy pr :: extendTrans xLTy prs

public export
StronglyConnex Nat LTE where
  order x y =
    case isLTE x y of
      Yes prf => Left prf
      No prfnot => Right (lteSuccLeft (notLTEImpliesGT prfnot))

public export
(sc : StronglyConnex a rel) => StronglyConnex a (flip rel) where
  order x y = order @{sc} y x

public export
(ts : Transitive a rel) => Transitive a (flip rel) where
  transitive x y = transitive @{ts} y x

public export
FlipSC : StronglyConnex a rel => StronglyConnex a (flip rel)
FlipSC = %search

public export
FlipTS : Transitive a rel => Transitive a (flip rel)
FlipTS = %search

public export
flipOrder : {rel : a -> a -> Type} -> (StronglyConnex a rel, Transitive a rel) -> (StronglyConnex a (flip rel), Transitive a (flip rel))
flipOrder _ = (FlipSC, FlipTS)

public export
stronglyConnexReflexive : (rel : a -> a -> Type) -> (StronglyConnex a rel) => {x : a} -> rel x x
stronglyConnexReflexive rel = case order x x of
  Left prf => prf
  Right prf => prf
