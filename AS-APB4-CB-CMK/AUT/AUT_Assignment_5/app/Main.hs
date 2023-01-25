module Main (main) where

import System.Environment
import System.IO
import Lib

launch :: [String] -> IO ()
launch [] = error "Not enough arguments"
launch [file] = do
    handle <- openFile file ReadMode
    contents <- hGetContents handle
    case nfaToGraphviz contents of
        Just transformed -> putStrLn transformed
        Nothing -> error "Error while parsing"
    hClose handle
launch _ = error "Too many arguments"

main :: IO ()
main = getArgs >>= launch
