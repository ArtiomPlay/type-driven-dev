module Prat12

import Data.List

%default total

data Binop : Type where
    Plus : Binop
    Times : Binop

data Exp : Type where
    Const : Nat -> Exp
    Op : Binop -> Exp -> Exp -> Exp

binopDenote : Binop -> Nat -> Nat -> Nat
binopDenote Plus k j = k + j
binopDenote Times k j = k * j

expDenote : Exp -> Nat
expDenote (Const k) = k
expDenote (Op x y z) = (binopDenote x) (expDenote y) (expDenote z)

e_text : expDenote (Op Plus (Const 1) (Const 2)) = 3
e_text = Refl

data Instr : Type where
    IConst : Nat -> Instr
    IOp : Binop -> Instr

Prog = List Instr
Stack = List Nat

instrDenote : Instr -> Stack -> Maybe Stack
instrDenote (IConst k) ks = Just (k :: ks)
instrDenote (IOp x) (y :: z :: xs) = Just (binopDenote x y z :: xs)
instrDenote (IOp x) _ = Nothing

progDenote : Prog -> Stack -> Maybe Stack
progDenote [] ks = Just ks
progDenote (x :: xs) ks with (instrDenote x ks)
  progDenote (x :: xs) ks | Nothing = Nothing
  progDenote (x :: xs) ks | (Just y) = progDenote xs y

appendAssociativeRev : (l ,c ,r : List a) -> (l ++ c) ++ r = l ++ (c ++ r)
appendAssociativeRev l c r = rewrite sym (appendAssociative l c r) in Refl

compile : Exp -> Prog
compile (Const k) = [ IConst k ]
compile (Op x y z) = (compile z) ++ (compile y) ++ [ IOp x ]

compileCorrect : (e : Exp) -> (p : Prog) -> (s : Stack) ->
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)
compileCorrect (Const k) p s = Refl
compileCorrect (Op x y z) p s =
    rewrite appendAssociativeRev (compile z) (compile y ++ IOp x :: []) p in
    rewrite compileCorrect z ((compile y ++ IOp x :: []) ++ p) s in
    rewrite appendAssociativeRev (compile y) (IOp x :: []) p in
    rewrite compileCorrect y (IOp x :: [] ++ p) (expDenote z :: s) in
    Refl
