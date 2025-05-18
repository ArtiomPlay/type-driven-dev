module MainProject

import Data.String
import Data.List
import Data.Vect

%default total

data InfIO : Type where
    Do : IO a -> (a -> Inf InfIO) -> InfIO
    Done : IO() -> InfIO

data Fuel' = Dry | More (Lazy Fuel')

data Evidence = EMP | Orbs | Box | Freezing | Ultraviolet | Writting | DOTS

Eq Evidence where
    (==) EMP EMP = True
    (==) Orbs Orbs = True
    (==) Box Box = True
    (==) Freezing Freezing = True
    (==) Ultraviolet Ultraviolet = True
    (==) Writting Writting = True
    (==) DOTS DOTS = True
    (==) _ _ = False

data Ghost : Type where
    MkGhost : (name : String) -> {n : Nat} -> (evidences : Vect n Evidence) -> Ghost

allEvidences : List Evidence
allEvidences = [EMP, Orbs, Box, Freezing, Ultraviolet, Writting, DOTS]

allGhosts : List Ghost
allGhosts = [
    MkGhost "Banshee" [Orbs,Ultraviolet,DOTS],
    MkGhost "Demon" [Freezing,Ultraviolet,Writting],
    MkGhost "Deogen" [Box,Writting,DOTS],
    MkGhost "Goryo" [EMP,Ultraviolet,DOTS],
    MkGhost "Hantu" [Orbs,Freezing,Ultraviolet],
    MkGhost "Jinn" [EMP,Freezing,Ultraviolet],
    MkGhost "Mare" [Orbs,Box,Writting],
    MkGhost "Moroi" [Box,Freezing,Writting],
    MkGhost "Myling" [EMP,Ultraviolet,Writting],
    MkGhost "Obake" [EMP,Orbs,Ultraviolet],
    MkGhost "Oni" [EMP,Freezing,DOTS],
    MkGhost "Onryo" [Orbs,Box,Freezing],
    MkGhost "Phantom" [Box,Ultraviolet,DOTS],
    MkGhost "Poltergeist" [Box,Ultraviolet,Writting],
    MkGhost "Raiju" [EMP,Orbs,DOTS],
    MkGhost "Revenant" [Orbs,Freezing,Writting],
    MkGhost "Shade" [EMP,Freezing,Writting],
    MkGhost "Spirit" [EMP,Box,Writting],
    MkGhost "Thaye" [Orbs,Writting,DOTS],
    MkGhost "The Mimic" [Orbs,Box,Freezing,Ultraviolet],
    MkGhost "The Twins" [EMP,Box,Freezing],
    MkGhost "Wraith" [EMP,Box,DOTS],
    MkGhost "Yokai" [Orbs,Box,DOTS],
    MkGhost "Yurei" [Orbs,Freezing,DOTS]
]

currentGhosts : List Ghost
currentGhosts = allGhosts

showEvidence : Evidence -> String
showEvidence e = case e of
                      EMP => "EMP 5 (EMP)"
                      Orbs => "Ghost Orbs (Orbs)"
                      Box => "Spirit Box (Box)"
                      Freezing => "Freezing Temperature (Freezing)"
                      Ultraviolet => "Ultraviolet (Ultraviolet)"
                      Writting => "Ghost Writting (Writting)"
                      DOTS => "D.O.T.S Projector (DOTS)"

showEvidenceList : List Evidence -> String
showEvidenceList evidences = case evidences of
                                  [] => "No evidences"
                                  _ => joinBy "\n" (map showEvidence evidences)

showGhost : Ghost -> String
showGhost (MkGhost name evidences) =
    name ++ " (" ++ joinBy ", " (map showEvidence (toList evidences)) ++ ")"

showGhostList : List Ghost -> String
showGhostList ghosts = case ghosts of
                            [] => "No ghosts"
                            _ => joinBy "\n" (map showGhost ghosts)


(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

(>>) : IO a -> Inf InfIO -> Inf InfIO
(>>) act next = Do act (\_ => next)

filterGhosts : List Evidence -> List Ghost
filterGhosts selected =
    filter (\(MkGhost _ evs) => all (`elem` (toList evs)) selected) allGhosts

parseEvidence : String -> Maybe Evidence
parseEvidence str = case toLower str of
                         "emp" => Just EMP
                         "orbs" => Just Orbs
                         "box" => Just Box
                         "freezing" => Just Freezing
                         "ultraviolet" => Just Ultraviolet
                         "writting" => Just Writting
                         "dots" => Just DOTS
                         _ => Nothing

handleInput : String -> List Evidence -> (String, List Evidence)
handleInput input checked =
    let parts = words input in
    case parts of
        ["ghosts"] => (showGhostList (filterGhosts checked), checked)
        ["ghosts", "all"] => (showGhostList allGhosts, checked)
        ["evidences"] => (showEvidenceList checked, checked)
        ["evidences", "all"] => (showEvidenceList allEvidences, checked)
        ["check", evStr] =>
            case parseEvidence evStr of
                Just ev =>
                    if elem ev checked then ("Already checked", checked)
                    else ("Checked " ++ showEvidence ev, ev :: checked)
                Nothing => ("Unknown evidence: " ++ evStr, checked)
        ["uncheck", evStr] =>
            case parseEvidence evStr of
                Just ev =>
                    if elem ev checked then ("Unchecked " ++ showEvidence ev, delete ev checked)
                    else ("Evidence not checked", checked)
                Nothing => ("Unknown evidence: " ++ evStr, checked)
        ["help"] => ("Available commands:\ncheck [evidence]\nuncheck [evidence]\nghosts\nghosts all\nevidences\nevidences all\nexit", checked)
        _ => ("Unknown command", checked)

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

loop : List Evidence -> InfIO
loop checked =
    Do (putStr "\n>>>") $ \_ =>
    Do getLine $ \input =>
        if toLower input == "exit" then
            Done (putStrLn "Exiting. Goodbye!")
            else
                case handleInput input checked of
                    (output, newChecked) => Do (putStrLn output) (\_ => loop newChecked)

covering
main : IO()
main = run forever (loop [])

testParseEvidence : parseEvidence "emp" = Just EMP
testParseEvidence = Refl

testParseEvidence' : parseEvidence "something" = Nothing
testParseEvidence' = Refl

testFilterGhosts : filterGhosts [Freezing, Ultraviolet, Writting] = [MkGhost "Demon" [Freezing, Ultraviolet, Writting]]
testFilterGhosts = Refl

testShowEvidenceList : showEvidenceList [EMP] = "EMP 5 (EMP)"
testShowEvidenceList = Refl

testShowEvidenceList' : showEvidenceList [EMP,Box] = "EMP 5 (EMP)\nSpirit Box (Box)"
testShowEvidenceList' = Refl

testShowGhost : showGhost (MkGhost "Spirit" [EMP, Box, Writting]) = "Spirit (EMP 5 (EMP), Spirit Box (Box), Ghost Writting (Writting))"
testShowGhost = Refl

testCheckUncheckSequence :
    let (_, s1) = handleInput "check emp" [] in
    let (_, s2) = handleInput "check box" s1 in
    let (_, s3) = handleInput "uncheck emp" s2 in
    s3 = [Box]
testCheckUncheckSequence = Refl

testAllSelectedIncluded : 
  let selected = [Freezing, Ultraviolet] in
  all (\(MkGhost _ evs) => all (\e => e `elem` (toList evs)) selected) (filterGhosts selected) = True
testAllSelectedIncluded = Refl
