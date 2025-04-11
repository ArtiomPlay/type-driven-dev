module Prat10
import Data.Stream
import Data.Nat
import Data.Double

%default total

everyOther : Stream a -> Stream a
everyOther (x :: y :: z) = x :: everyOther z

sqrt : Nat -> Double -> Stream Double
sqrt n a = a :: sqrt n ((a + ((cast n) / a)) / 2.0)

nextGuess : Double -> Double -> Double
nextGuess x guess = (guess + (x / guess)) / 2.0

boundedSqrt' : Double -> Double -> Double -> Nat -> Double
boundedSqrt' n delta guess 0 = guess
boundedSqrt' n delta guess (S k) =
    let newGuess=nextGuess n guess in
        if abs (n - newGuess*newGuess) < delta then
            newGuess
        else
            boundedSqrt' n delta newGuess k

boundedSqrt : Nat -> Double -> Double
boundedSqrt n delta =
    let x = cast n
        initialGuess = x / 2.0
    in boundedSqrt' x delta initialGuess 100

data InfList : Type -> Type where
    (::) : (value : e) -> Inf (InfList e) -> InfList e


-- x > N -> x..inf
-- x <= N -> x..N
countTrap : Nat -> Nat -> Stream Nat
countTrap x n = ?countTrap_rhs
