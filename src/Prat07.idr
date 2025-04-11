module Prat07

import Data.Nat

%default total

data Even : Nat -> Type where
    EvenZero : Even 0
    EvenNext : {x : Nat} -> Even x -> Even (S (S x))

data Odd : Nat -> Type where
    OddOne : Odd 1
    OddNext : {x : Nat} -> Odd x -> Odd (S (S x))

oddToEven : {x : Nat} -> Odd x -> Even (S x)
oddToEven OddOne = EvenNext EvenZero
oddToEven (OddNext y) = EvenNext (oddToEven y)

oddToEven' : Odd (S x) -> Even x
oddToEven' OddOne = EvenZero
oddToEven' (OddNext OddOne) = EvenNext EvenZero
oddToEven' (OddNext (OddNext y)) = EvenNext (oddToEven' (OddNext y))

evenOrOdd : (x : Nat) -> Either (Even x) (Odd x)
evenOrOdd 0 = Left EvenZero
evenOrOdd (S 0) = Right OddOne
evenOrOdd (S (S k)) = case evenOrOdd k of
                           (Left x) => Left (EvenNext x)
                           (Right x) => Right (OddNext x)

task4 : Even x -> (y : Nat ** (GT y x,Even y))

task5 : (p,q : a -> Type) -> (x : a ** (p x, q x)) -> ((y : a ** (p y)), (z : a ** (q z)))
task5 p q ((fst ** (x, y))) = ((fst ** x), (fst ** y))
