module Prat06

import Data.Vect

%default total

task1 : a -> b -> Either (Not a) b
task1 x y = Right y

task2 : (p,q) -> Either p q
task2 (x, y) = Left x

task3 : Either (p,q) r -> (Either p r,Either q r)
task3 (Left x) = (Left (fst x), Left (snd x))
task3 (Right x) = (Right x, Right x)

task3' : (Either p r, Either q r) -> Either (p,q) r
task3' ((Left x), (Left y)) = Left (x, y)
task3' ((Left x), (Right y)) = Right y
task3' ((Right x), _) = Right x

task4 : p -> Not (Not p)
task4 x f = f x

task5 : (p -> Not p) -> Not p
task5 f x = f x x

task5' : (p -> (p -> Void)) -> (p -> Void)
task5' f x = f x x

task6 : Not (p,q) -> (p -> Not q)
task6 f x y = f (x, y)

task6' : ((p,q) -> Void) -> p -> q -> Void
task6' f x y = f (x, y)

contr_position : (p -> q) -> (q -> Void) -> (p -> Void)
contr_position f g x = g (f x)
