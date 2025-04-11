module MainProject

import Data.String
import System

%default total

data InfIO : Type where
    Do : IO a -> (a -> Inf InfIO) -> InfIO
    Done : IO() -> InfIO

data Fuel' = Dry | More (Lazy Fuel')

covering
forever : Fuel'
forever = More forever

total
run : Fuel' -> InfIO -> IO()
run Dry _ = putStrLn "Out of fuel. Goodbye!"
run (More f) (Do action next) = do
    result <- action
    run f (next result)
run _ (Done final) = final

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

(>>) : IO a -> Inf InfIO -> Inf InfIO
(>>) act next = Do act (\_ => next)

respondTo : String -> String
respondTo cmd = case toLower cmd of
                     "help" => "Help"
                     _ => "Unknown command"

loop : InfIO
loop =
    Do (putStr "\n>>>") $ \_ =>
    Do getLine $ \input =>
        if toLower input == "exit" then
            Done (putStrLn "Exiting. Goodbye!")
            else
                Do (putStrLn (respondTo input)) (\_ => loop)

covering
main : IO()
main = run forever loop
