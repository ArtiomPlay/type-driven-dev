module Prat15
import System.File
import System.File.ReadWrite
import Data.Fuel

%default total

covering
    testFileReading : IO ()
testFileReading = do
    Right file <- openFile "src/test.txt" Read | Left err => putStrLn "Error opening file"
    Right res <- fGetChar file | Left err => putStrLn "Error reading file"
    putStrLn (show res)
    closeFile file

namespace FH
    export
    data FileHandler : Type where
        MkFH : File -> FileHandler

    export
    openF : String -> Mode -> IO (Either FileError FileHandler)
    openF f m = do
        Right f <- openFile f m | Left err => pure $ Left err
        pure $ Right (MkFH f)

    export
    closeF : (1 fh : FileHandler) -> IO ()
    closeF (MkFH f) = do
        closeFile f

    export
    getChar : (1 fh : FileHandler) -> IO (Either FileError (Char, FileHandler))
    getChar (MkFH f) = do
        Right r <- fGetChar f | Left err => pure $ Left err
        pure $ Right (r, (MkFH f))

testFileLinear : IO ()
testFileLinear = do
    Right fh <- openF "src/test.txt" Read | Left err => putStrLn "Error opening file"
    Right (res, fh') <- getChar fh | Left err => putStrLn "Error reading file"
    putStrLn $ show res
    closeF fh'

