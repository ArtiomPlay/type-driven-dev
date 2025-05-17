module Prat14
import Data.Nat
import Data.List

%default total

app_assoc : (lst1, lst2, lst3 : List a) -> (lst1 ++ lst2) ++ lst3 = lst1 ++ (lst2 ++ lst3)
app_assoc [] lst2 lst3 = Refl
app_assoc (x :: xs) lst2 lst3 = rewrite app_assoc xs lst2 lst3 in Refl

app_length : (lst1, lst2 : List a) -> length (lst1 ++ lst2) = length lst1 + length lst2
app_length [] lst2 = Refl
app_length (x :: xs) lst2 = rewrite app_length xs lst2 in Refl

rev : (lst : List a) -> List a
rev [] = []
rev (x :: xs) = rev xs ++ [x]

rev_length : (lst : List a) -> length (rev lst) = length lst
rev_length [] = Refl
rev_length (x :: xs) = rewrite sym (rev_length xs) in 
    rewrite app_length (rev xs) [x] in
    rewrite plusCommutative 1 (length (rev xs)) in Refl

tl : (lst : List a) -> List a
tl [] = []
tl (x :: xs) = xs

tl_length_pred : (lst : List a) -> pred (length lst) = length (tl lst)
tl_length_pred [] = Refl
tl_length_pred (x :: xs) = Refl
