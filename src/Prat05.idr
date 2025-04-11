module Prat05

import Data.Vect
import Decidable.Equality

%default total

plusNz : (n : Nat) -> n + Z = n
plusNz 0 = Refl
plusNz (S k) =
    let indH = plusNz k in
    cong S indH
    
plus_n_Sm : (n, m : Nat) -> S (n+m) = n + S m
plus_n_Sm 0 m = Refl
plus_n_Sm (S k) m =
    let indH = plus_n_Sm k m in
    rewrite indH in Refl

plus_comm : (n, m : Nat) -> n + m = m + n
plus_comm 0 m = rewrite plusNz m in Refl
plus_comm (S k) m =
    let indH = plus_comm k m in
    rewrite indH in
    rewrite plus_n_Sm m k in
    Refl

plus_assoc : (n,m,p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc 0 m p = Refl
plus_assoc (S k) m p = rewrite plus_assoc k m p in Refl

mul_comm_help : (k : Nat) -> (m : Nat) -> mult k (S m) = plus k (mult k m)
mul_comm_help 0 m = Refl
mul_comm_help (S k) m =
    let intH = mul_comm_help k m in
    rewrite intH in
    rewrite plus_assoc k m (k*m) in
    rewrite plus_assoc m k (k*m) in
    rewrite plus_comm m k in Refl

mul_comm : (n,m : Nat) -> n * m = m * n
mul_comm 0 0 = Refl
mul_comm 0 (S k) = mul_comm 0 k
mul_comm (S k) m =
    rewrite mul_comm k m in
    rewrite mul_comm_help m k in
    Refl

plus_swap : (n,m,p : Nat) -> n + (m + p) = m + (n + p)
plus_swap n m p =
    rewrite plus_assoc n m p in
    rewrite plus_assoc m n p in
    rewrite plus_comm n m in Refl

hUnequal : DecEq a => (xs:Vect n a) -> (ys:Vect n a) -> (contra:(x=y) -> Void) -> (x::xs)=(y::ys) -> Void
hUnequal xs xs contra Refl = contra Refl

tUnequal : DecEq a => (xs:Vect n a) -> (ys:Vect n a) -> (contra:(xs=ys) -> Void) -> (x::xs)=(y::ys) -> Void
tUnequal xs xs contra Refl = contra Refl
