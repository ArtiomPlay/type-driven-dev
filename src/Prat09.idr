module Prat09

import Data.List
import Data.List.Views

%default total

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | (SplitRecOne x) = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec) =
    merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

data TakeN : List a -> Type where
    Fever : (xs : List a) -> TakeN xs
    Exact : (xs : List a) -> (next : List a) -> TakeN (xs ++ next)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN 0 xs = Exact [] xs
takeN n [] = Fever []
takeN n (x :: xs) with (takeN n xs)
  takeN n (x :: xs) | (Fever xs) = Fever (x :: xs)
  takeN n (x :: (ys ++ next)) | (Exact ys next) = Exact (x :: ys) next

covering
groupBy' : (n : Nat) -> (xs : List a) -> (List (List a))
groupBy' _ [] = []
groupBy' 0 xs = [xs]
groupBy' n xs with (takeN n xs)
  groupBy' n xs | (Fever xs) = [xs]
  groupBy' n (ys ++ next) | (Exact ys next) = ys :: (groupBy' n next)

data TakeNRec : List a -> Type where
    FeverRec : (xs : List a) -> TakeNRec xs
    ExactRec : (xs : List a) -> (next : List a) -> (rec : TakeNRec next) -> TakeNRec (xs ++ next)


takeNRec : (n : Nat) -> (xs : List a) -> TakeNRec xs
takeNRec 0 xs = ExactRec [] xs (FeverRec xs)
takeNRec n [] = FeverRec []
takeNRec n (x :: xs) with (takeNRec n xs)
    takeNRec n (x :: xs) | (FeverRec xs) = FeverRec (x :: xs)
    takeNRec n (x :: (ys ++ next)) | (ExactRec ys next rec) = ExactRec (x :: ys) next rec

groupBy'Rec : (n : Nat) -> (xs : List a) -> (List (List a))
groupBy'Rec _ [] = []
groupBy'Rec 0 xs = [xs]
groupBy'Rec n xs with (takeNRec n xs)
  groupBy'Rec n xs | (FeverRec xs) = [xs]
  groupBy'Rec n (ys ++ next) | (ExactRec ys next rec) = ys :: (groupBy'Rec n next | rec)
