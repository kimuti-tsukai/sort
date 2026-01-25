module Sort.TimSort

import Data.Vect
import Data.Vect.Quantifiers
import Data.List
import Control.Order
import Control.Relation
import Control.WellFounded

import Proofs.Permutation
import Proofs.Sorted
import Utils.Relation
import Utils.Vect
import Sort
import Sort.InsertionSort
import Sort.MergeSort

%default total

minRunLength : Nat
minRunLength = 64

SortedEither : (rel : a -> a -> Type) -> Vect n a -> Type
SortedEither rel xs = Either (Sorted rel xs) (Sorted (flip rel) xs)

Runs : (a : Type) -> (rel : a -> a -> Type) -> Type
Runs a rel = List (m : Nat ** v : Vect m a ** SortedEither rel v)

AlignedRuns : (a : Type) -> (rel : a -> a -> Type) -> Type
AlignedRuns a rel = List (m : Nat ** v : Vect m a ** Sorted rel v)

sumRunsLength : Runs a rel -> Nat
sumRunsLength [] = 0
sumRunsLength ((n ** _) :: xs) = n + sumRunsLength xs

sumRunsLengthAligned : AlignedRuns a rel -> Nat
sumRunsLengthAligned [] = 0
sumRunsLengthAligned ((n ** _) :: xs) = n + sumRunsLengthAligned xs

concatAllRuns : (xs : Runs a rel) -> Vect (sumRunsLength xs) a
concatAllRuns [] = []
concatAllRuns ((m ** v ** _) :: vs) = v ++ concatAllRuns vs

concatAllRunsAligned : (xs : AlignedRuns a rel) -> Vect (sumRunsLengthAligned xs) a
concatAllRunsAligned [] = []
concatAllRunsAligned ((m ** v ** _) :: vs) = v ++ concatAllRunsAligned vs

makeRuns :
  (rel : a -> a -> Type)
  -> (StronglyConnex a rel, Transitive a rel)
  => {n : Nat} -> (xs : Vect n a)
  -> (runs : Runs a rel ** lenPrf : n = sumRunsLength {rel} runs ** xs = (rewrite lenPrf in concatAllRuns runs))
makeRuns rel [] = ([] ** Refl ** Refl)
makeRuns rel @{(sc, _)} (x :: xs) with (makeRuns rel xs)
  _ | ([] ** lenPrf ** conPrf) = ([(1 ** [x] ** Left $ Cons x Nil Nil)] ** (cong S lenPrf) ** (rewrite sym lenPrf in cong (x ::) conPrf))
  _ | ((0 ** [] ** _) :: runs ** lenPrf ** conPrf) = ((1 ** [x] ** Left $ Cons x Nil Nil) :: runs ** (cong S lenPrf) ** (rewrite sym lenPrf in cong (x ::) conPrf))
  _ | ((1 ** [y] ** _) :: runs ** lenPrf ** conPrf) =
    case order x y of
      Left xLTy => ((2 ** [x, y] ** Left $ Cons x (xLTy :: Nil) (Cons y Nil Nil)) :: runs ** (cong S lenPrf) ** (rewrite sym lenPrf in cong (x ::) conPrf))
      Right xGTy => ((2 ** [x, y] ** Right $ Cons x (xGTy :: Nil) (Cons y Nil Nil)) :: runs ** (cong S lenPrf) ** (rewrite sym lenPrf in cong (x ::) conPrf))
  _ | ((S (S len) ** y :: z :: ys ** (Left sortedZYs@(Cons _ yLTzys sortedYs))) :: runs ** lenPrf ** conPrf) =
    case order @{sc} x y of
      Left xLTy => ((S (S (S len)) ** x :: y :: z :: ys ** Left $ Cons x (xLTy :: (extendTrans xLTy yLTzys)) sortedZYs) :: runs ** (cong S lenPrf) ** (rewrite sym lenPrf in cong (x ::) conPrf))
      Right xGTy => ((1 ** [x] ** Left $ Cons x Nil Nil) :: ((S (S len)) ** y :: z :: ys ** Left sortedZYs) :: runs ** (cong S lenPrf) ** (rewrite sym lenPrf in cong (x ::) conPrf))
  _ | ((S (S len) ** y :: z :: ys ** (Right sortedZYs@(Cons _ yGTzys sortedYs))) :: runs ** lenPrf ** conPrf) =
    case order @{sc} x y of
      Left xLTy => ((1 ** [x] ** Left $ Cons x Nil Nil) :: ((S (S len)) ** y :: z :: ys ** Right sortedZYs) :: runs ** (cong S lenPrf) ** (rewrite sym lenPrf in cong (x ::) conPrf))
      Right xGTy => ((S (S (S len)) ** x :: y :: z :: ys ** Right $ Cons x (xGTy :: (extendTrans @{FlipTS} xGTy yGTzys)) sortedZYs) :: runs ** (cong S lenPrf) ** (rewrite sym lenPrf in cong (x ::) conPrf))

reverseSorted : {rel : a -> a -> Type} -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> Sorted rel xs -> (v : Vect n a ** (Permutation xs v, Sorted (flip rel) v))
reverseSorted [] Nil = ([] ** (PermNil, Nil))
reverseSorted {n = S len} (x :: xs) (Cons _ xLTxs sortedXs) = rewrite sym $ plusZeroRightNeutral len in rewrite sym $ appendNilRightNeutral xs in revAcc x xs sortedXs xLTxs [] Nil Nil
  where
    revAcc :
      (current : a)
      -> {left : Nat} -> (xs : Vect left a)
      -> Sorted rel xs -> All (rel current) xs
      -> {right : Nat} -> (acc : Vect right a)
      -> Sorted (flip rel) acc -> All ((flip rel) current) acc
      -> (zs : Vect (S left + right) a ** (Permutation (current :: xs ++ acc) zs, Sorted (flip rel) zs))
    revAcc c [] Nil Nil acc sortedAcc cGTacc = (c :: acc ** (permRefl, Cons c cGTacc sortedAcc))
    revAcc c {left = S len} (x :: xs) (Cons _ xLTxs sortedXs) (cLTx :: cLTxs) acc sortedAcc cGTacc =
      let
        xGTacc = extendTrans @{FlipTS} cLTx cGTacc
        (zs ** (permXXsCAccAndZs, sortedZs)) = revAcc x xs sortedXs xLTxs (c :: acc) (Cons c cGTacc sortedAcc) (cLTx :: xGTacc)
        perm = PermTrans (PermSwap c x (xs ++ acc)) (PermSkip x (permMoveHeadToMiddle c xs acc))
        perm' = PermTrans perm (rewrite plusSuccRightSucc len right in permXXsCAccAndZs)
      in ((rewrite plusSuccRightSucc len right in zs) ** (perm', (rewrite plusSuccRightSucc len right in sortedZs)))

alignRunsDirection :
  {rel : a -> a -> Type} -> (StronglyConnex a rel, Transitive a rel)
  => (runs : Runs a rel)
  -> (alignedRuns : AlignedRuns a rel ** lenPrf : sumRunsLength runs = sumRunsLengthAligned alignedRuns ** (Permutation (concatAllRuns runs) (rewrite lenPrf in concatAllRunsAligned alignedRuns)))
alignRunsDirection [] = ([] ** Refl ** PermNil)
alignRunsDirection ((n ** v ** dir) :: runs) =
  let
    (alignedRuns ** lenPrf ** perm) = alignRunsDirection runs
  in case dir of
    Left sortedV => ((n ** v ** sortedV) :: alignedRuns ** (cong (n +) lenPrf) ** permAppendRight v perm)
    Right sortedFlipV =>
      let (aligned ** (permVAligned, sortedAligned)) = reverseSorted v sortedFlipV
      in ((n ** aligned ** sortedAligned) :: alignedRuns ** (cong (n +) lenPrf) ** (permAppend permVAligned perm))

[SizedRuns] Sized (AlignedRuns a rel) where
  size xs = length xs + sumRunsLengthAligned xs

fillRun :
  {rel : a -> a -> Type} -> (StronglyConnex a rel, Transitive a rel)
  => (n : Nat) -> (v : Vect n a) -> Sorted rel v
  -> (runs : AlignedRuns a rel)
  -> SizeAccessible @{SizedRuns} runs
  -> (m : Nat ** extendedRun : Vect m a ** sortedExtendedRun : Sorted rel extendedRun ** remainingRuns : AlignedRuns a rel ** lenPrf : LTE (length remainingRuns) (length runs) ** sizePrf : n + sumRunsLengthAligned runs = m + sumRunsLengthAligned remainingRuns ** Permutation (v ++ concatAllRunsAligned runs) (rewrite sizePrf in extendedRun ++ concatAllRunsAligned remainingRuns))
fillRun n v sortedV [] _ = (n ** v ** sortedV ** [] ** reflexive ** Refl ** permRefl)
fillRun n v sortedV ((0 ** [] ** _) :: rest) (Access acc) with (n < minRunLength)
  _ | False = (n ** v ** sortedV ** rest ** lteSuccRight reflexive ** Refl ** permRefl)
  _ | True =
    let (l ** extendedRun ** sortedExtendedRun ** remainingRuns ** lenPrf ** sizePrf ** perm) = fillRun n v sortedV rest (acc rest reflexive)
    in (l ** extendedRun ** sortedExtendedRun ** remainingRuns ** lteSuccRight lenPrf ** sizePrf ** perm)
fillRun n v sortedV ((S k ** next :: sup ** (Cons _ nextLTsup sortedSup)) :: rest) (Access acc) with (n < minRunLength)
  _ | False = (n ** v ** sortedV ** ((S k ** next :: sup ** (Cons _ nextLTsup sortedSup)) :: rest) ** reflexive ** Refl ** permRefl)
  _ | True =
    let
      (newV ** (permNextVAndNewV, newSorted)) = insertInOrder rel next v sortedV
      smallerSum = rewrite sym $ plusSuccRightSucc (length rest) (k + sumRunsLengthAligned rest) in reflexive
      (l ** extendedRun ** sortedExtendedRun ** remainingRuns ** lenPrf ** sizePrf ** perm) = fillRun (S n) newV newSorted ((k ** sup ** sortedSup) :: rest) (acc ((k ** sup ** sortedSup) :: rest) smallerSum)
      perm' = PermTrans (permAppendLeft permNextVAndNewV (sup ++ concatAllRunsAligned rest)) perm
      perm'' = PermTrans (permSym $ permMoveHeadToMiddle next v (sup ++ concatAllRunsAligned rest)) perm'
    in rewrite sym $ plusSuccRightSucc n (k + sumRunsLengthAligned rest) in (l ** extendedRun ** sortedExtendedRun ** remainingRuns ** lenPrf ** sizePrf ** perm'')

lteAddLeft : (n : Nat) -> LTE n (m + n)
lteAddLeft n = rewrite plusCommutative m n in lteAddRight n

extendToMinRun :
  {rel : a -> a -> Type} -> (StronglyConnex a rel, Transitive a rel)
  => (runs : AlignedRuns a rel)
  -> SizeAccessible @{SizedRuns} runs
  -> (extendedRuns : AlignedRuns a rel ** sizePrf : sumRunsLengthAligned runs = sumRunsLengthAligned extendedRuns ** (Permutation (concatAllRunsAligned runs) (rewrite sizePrf in concatAllRunsAligned extendedRuns)))
extendToMinRun [] _ = ([] ** Refl ** PermNil)
extendToMinRun ((l ** run ** sorted) :: runs) (Access acc) =
  let
    lte' = LTESucc $ plusLteMonotoneLeft (length runs) (sumRunsLengthAligned runs) (l + sumRunsLengthAligned runs) (lteAddLeft (sumRunsLengthAligned runs))
    (n' ** v' ** sorted' ** remaining ** lenPrf ** sizePrf ** perm) = fillRun l run sorted runs (acc runs lte')
    lte'' = rewrite sizePrf in LTESucc $ plusLteMonotone lenPrf (lteAddLeft (sumRunsLengthAligned remaining))
    (restExtended ** restPrf ** restPerm) = extendToMinRun remaining (acc remaining lte'')
    finalSizePrf = rewrite sym restPrf in sizePrf
    finalPerm = PermTrans perm (rewrite sizePrf in permAppendRight v' restPerm)
  in ((n' ** v' ** sorted') :: restExtended ** finalSizePrf ** finalPerm)

mergeRunsWithRule :
  {rel : a -> a -> Type} -> (StronglyConnex a rel, Transitive a rel)
  => (runs : AlignedRuns a rel)
  -> SizeAccessible runs
  -> (mergedRuns : AlignedRuns a rel ** sizePrf : sumRunsLengthAligned runs = sumRunsLengthAligned mergedRuns ** Permutation (concatAllRunsAligned runs) (rewrite sizePrf in concatAllRunsAligned mergedRuns))
mergeRunsWithRule [] _ = ([] ** Refl ** PermNil)
mergeRunsWithRule [run@(_ ** _ ** _)] _ = ([run] ** Refl ** permRefl)
mergeRunsWithRule [run1@(_ ** _ ** _), run2] _ = ([run1, run2] ** Refl ** permRefl)
mergeRunsWithRule ((n1 ** v1 ** s1) :: (n2 ** v2 ** s2) :: (n3 ** v3 ** s3) :: runs) (Access acc) with (n2 < n3 && (n1 + n2) < n3)
  _ | True =
    let (mergedRuns ** sizePrf ** perm) = mergeRunsWithRule ((n2 ** v2 ** s2) :: (n3 ** v3 ** s3) :: runs) (acc ((n2 ** v2 ** s2) :: (n3 ** v3 ** s3) :: runs) reflexive)
    in ((n1 ** v1 ** s1) :: mergedRuns ** (cong (n1 +) sizePrf) ** (permAppendRight v1 perm))
  _ | False =
    if (n1 >= n3) then
      let
        (v23 ** (permV2V3AndV23, sortedV23)) = mergeSorted rel v2 s2 v3 s3
        (mergedRuns ** sizePrf ** perm) = mergeRunsWithRule ((n1 ** v1 ** s1) :: (n2 + n3 ** v23 ** sortedV23) :: runs) (acc ((n1 ** v1 ** s1) :: (n2 + n3 ** v23 ** sortedV23) :: runs) reflexive)
        sizePrf' = rewrite plusAssociative n2 n3 (sumRunsLengthAligned runs) in sizePrf
        perm' = rewrite appendAssociative v2 v3 (concatAllRunsAligned runs) in rewrite plusAssociative n2 n3 (sumRunsLengthAligned runs) in PermTrans (permAppendRight v1 (permAppendLeft permV2V3AndV23 (concatAllRunsAligned runs))) perm
      in (mergedRuns ** sizePrf' ** perm')
    else
      let
        (v12 ** (permV1V2AndV12, sortedV12)) = mergeSorted rel v1 s1 v2 s2
        (mergedRuns ** sizePrf ** perm) = mergeRunsWithRule ((n1 + n2 ** v12 ** sortedV12) :: (n3 ** v3 ** s3) :: runs) (acc ((n1 + n2 ** v12 ** sortedV12) :: (n3 ** v3 ** s3) :: runs) reflexive)
        sizePrf' = rewrite plusAssociative n1 n2 (n3 + sumRunsLengthAligned runs) in sizePrf
        perm' = rewrite appendAssociative v1 v2 (v3 ++ concatAllRunsAligned runs) in rewrite plusAssociative n1 n2 (n3 + sumRunsLengthAligned runs) in PermTrans (permAppendLeft permV1V2AndV12 (v3 ++ concatAllRunsAligned runs)) perm
      in (mergedRuns ** sizePrf' ** perm')

mergeAllRuns : {rel : a -> a -> Type} -> (StronglyConnex a rel, Transitive a rel) => (runs : AlignedRuns a rel) -> (v : Vect (sumRunsLengthAligned runs) a ** (Permutation (concatAllRunsAligned runs) v, Sorted rel v))
mergeAllRuns runs = rewrite sym $ plusZeroRightNeutral (sumRunsLengthAligned runs) in rewrite sym $ appendNilRightNeutral (concatAllRunsAligned runs) in loop runs [] Nil
  where
    loop : (runs : AlignedRuns a rel) -> {n : Nat} -> (acc : Vect n a) -> Sorted rel acc -> (v : Vect (sumRunsLengthAligned runs + n) a ** (Permutation (concatAllRunsAligned runs ++ acc) v, Sorted rel v))
    loop [] acc sorted = (acc ** (permRefl, sorted))
    loop ((m ** v ** s) :: runs) acc sorted =
      let
        (newV ** (permVNewV, sortedNewV)) = mergeSorted rel v s acc sorted
        (mergedAll ** (permRunsNewVAndMergedAll, sortedMergedAll)) = loop runs newV sortedNewV
        perm' = PermTrans (permAppendRight (concatAllRunsAligned runs) permVNewV) permRunsNewVAndMergedAll
        perm'' = PermTrans (permAppendLeft (permAppendCommutative v (concatAllRunsAligned runs)) acc) (rewrite plusCommutative m (sumRunsLengthAligned runs) in rewrite sym $ plusAssociative (sumRunsLengthAligned runs) m n in rewrite (sym $ appendAssociative (concatAllRunsAligned runs) v acc) in perm')
      in (
        rewrite plusCommutative m (sumRunsLengthAligned runs) in rewrite sym $ plusAssociative (sumRunsLengthAligned runs) m n in mergedAll **
        (
          perm'',
          rewrite plusCommutative m (sumRunsLengthAligned runs) in rewrite sym $ plusAssociative (sumRunsLengthAligned runs) m n in sortedMergedAll
        )
      )

export
timSort : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => SortAlgorithm a rel
timSort rel xs =
  let
    (runs ** sizePrf ** eqPrf) = makeRuns rel xs
    (alignedRuns ** sizePrf' ** perm) = alignRunsDirection runs
    (extendedRuns ** sizePrf'' ** perm') = extendToMinRun alignedRuns (sizeAccessible @{SizedRuns} alignedRuns)
    (mergedWithRule ** sizePrf''' ** perm'') = mergeRunsWithRule extendedRuns (sizeAccessible extendedRuns)
    (merged ** (perm''', sortedMerged)) = mergeAllRuns mergedWithRule
    finalSizePrf = trans sizePrf (trans sizePrf' (trans sizePrf'' sizePrf'''))
    finalPerm = PermTrans perm (rewrite sizePrf' in PermTrans perm' (rewrite sizePrf'' in PermTrans perm'' (rewrite sizePrf''' in perm''')))
  in rewrite finalSizePrf in (merged ** (rewrite eqPrf in rewrite sym finalSizePrf in rewrite sizePrf in finalPerm, sortedMerged))
