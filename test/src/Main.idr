module Main

import System.Clock
import System.Random

import Data.Nat
import Data.Vect
import Data.List
import Control.Order
import Control.Relation

import Utils.Relation
import Proofs.Permutation
import Proofs.Sorted
import Sort.InsertionSort
import Sort.MergeSort
import Sort.QuickSort
import Sort.TimSort

benchOnce : (before : () -> IO a) -> (a -> IO b) -> IO (Clock Duration)
benchOnce before f = do
    args <- before ()
    start <- clockTime Monotonic
    result <- f args
    end <- clockTime Monotonic
    pure (timeDifference end start)

bench : (n : Nat) -> (before : () -> IO a) -> (a -> IO b) -> IO (List (Clock Duration))
bench n before f = sequence $ replicate n (benchOnce before f)

average : List (Clock Duration) -> Integer
average durations = sum (map toNano durations) `div` (cast (length durations))

randomNats : (n : Nat) -> IO (Vect n Nat)
randomNats n = do
    v <- sequence $ replicate n (rndFin 1_000_000)
    pure (map finToNat v)

sortBench :
    (algo : {a : Type} -> (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v)))
    -> (len : Nat)
    -> (time : Nat)
    -> IO Integer
sortBench algo len time = average <$> bench time before f
where
    before : () -> IO (Vect len Nat)
    before () = randomNats len

    f : Vect len Nat -> IO ()
    f v = do
        let _ = algo LTE v
        pure ()

insertionSort' : (rel : a -> a -> Type) -> (StronglyConnex a rel, Transitive a rel) => {n : Nat} -> (xs : Vect n a) -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
insertionSort' rel xs = insertionSort rel xs

main : IO ()
main = do
    let len = 100000
    let time = 10

    putStrLn "Insertion Sort"
    result <- sortBench insertionSort' len time
    printLn result

    putStrLn "Merge Sort"
    result <- sortBench mergeSort len time
    printLn result

    putStrLn "Quick Sort"
    result <- sortBench quickSort len time
    printLn result

    putStrLn "Tim Sort"
    result <- sortBench timSort len time
    printLn result
