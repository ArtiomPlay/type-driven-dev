module Prat08

%default total

-- data type: List a, a -> b, List b, lb made from la using a -> b
data ListProj : {a : Type} -> {b : Type} -> (op : a -> b) -> (la : List a) -> (lb : List b) -> Type where
    MkListProj : ListProj op la (map op la)

data ListProj' : {a : Type} -> {b : Type} -> (op : a -> b) -> (la : List a) -> (lb : List b) -> Type where
    MkListEmpty : ListProj' op [] []
    MkListElem : ListProj' op xs ys -> ListProj' op (x :: xs) (op x :: ys)

listProjConstr1 : {a : Type} -> {b : Type} -> (la : List a) -> (op : a -> b) -> (lb : List b ** ListProj op la lb)
listProjConstr1 la op = (map op la ** MkListProj)

listProjConstr1' : {a : Type} -> {b : Type} -> (la : List a) -> (op : a -> b) -> (lb : List b ** ListProj' op la lb)
listProjConstr1' [] op = ([] ** MkListEmpty)
listProjConstr1' (x :: xs) op = case listProjConstr1' xs op of
                          (([] ** snd)) => ([op x] ** MkListElem snd)
                          (((y :: ys) ** snd)) => (op x :: (y :: ys) ** MkListElem snd)

listProjPrf : {a : Type} -> {b : Type} ->
                {la : List a} -> {op : a -> b} ->
                {lb : List b} -> (ListProj' op la lb) -> (lb = map op la)
listProjPrf MkListEmpty = Refl
listProjPrf (MkListElem x) = case listProjPrf x of
                                  Refl => Refl
