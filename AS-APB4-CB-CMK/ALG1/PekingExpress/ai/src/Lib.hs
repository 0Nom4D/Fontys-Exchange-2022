module Lib
  ( myMain,
  )
where

import Control.Monad
import Data.Function
import Data.List
import Options.Applicative
import System.IO
import Text.JSON.Generic

data Options = Options
  { filename :: String,
    otherPos :: Int
  }

data Locations = Locations
  { number :: Int,
    critical :: [Int]
  }
  deriving (Show)

data Roads = Roads
  { aRoads :: [Int],
    bRoads :: [Int],
    price :: [Int]
  }
  deriving (Show)

data MapData = MapData
  { locations :: Locations,
    roads :: Roads,
    startLocation :: Int,
    budget :: Int
  }
  deriving (Show)

(!) :: (JSON a) => JSObject JSValue -> String -> Result a
(!) = flip valFromObj

instance JSON Locations where
  showJSON = undefined

  readJSON (JSObject obj) =
    Locations
      <$> obj ! "number"
      <*> obj ! "critical"
  readJSON _ = mzero

instance JSON Roads where
  showJSON = undefined

  readJSON (JSObject obj) =
    Roads
      <$> obj ! "a"
      <*> obj ! "b"
      <*> obj ! "price"
  readJSON _ = mzero

instance JSON MapData where
  showJSON = undefined

  readJSON (JSObject obj) =
    MapData
      <$> obj ! "Locations"
      <*> obj ! "Roads"
      <*> obj ! "StartLocation"
      <*> obj ! "Budget"
  readJSON _ = mzero

version :: String
version = "PekingExpressAI 0.1"

filenameParser :: Parser String
filenameParser =
  strOption
    ( long "filename"
        <> short 'f'
        <> help "Filename of the JSON data"
    )

otherPosParser :: Parser Int
otherPosParser =
  option
    auto
    ( long "playerPos"
        <> short 'p'
        <> help "Other player position"
    )

optionParser :: Parser Options
optionParser =
  Options
    <$> filenameParser
    <*> otherPosParser
    <* infoOption
      version
      ( long "version"
          <> short 'v'
          <> help "Display version and exit"
      )

myMain :: IO ()
myMain = launchAI =<< execParser opts
  where
    opts =
      info
        (optionParser <**> helper)
        ( fullDesc
            <> progDesc "AI to solve the PekingExpress problem"
            <> header "A very good AI trust me ;)"
        )

allPaths :: Int -> [(Int, Int, Int)] -> [Int] -> [[Int]]
allPaths start graph traversed =
  nextLists
  where
    curNodes = filter (\(a, b, _) -> (a == start && notElem b traversed) || (b == start && notElem a traversed)) graph
    nextStarts = map (\(a, b, _) -> if a == start then b else a) curNodes
    nextLists =
      if null curNodes
        then [[start]]
        else map (start :) $ concatMap (\x -> allPaths x graph (start : traversed)) nextStarts

extractRoads :: Roads -> [(Int, Int, Int)]
extractRoads (Roads [] _ _) = []
extractRoads (Roads _ [] _) = []
extractRoads (Roads _ _ []) = []
extractRoads (Roads (a : as) (b : bs) (p : ps)) =
  (a, b, p) : extractRoads (Roads as bs ps)

getBudgetNodes :: Int -> Int -> [(Int, Int, Int)] -> Int
getBudgetNodes _ _ [] = error "No"
getBudgetNodes a b ((xa, xb, xc) : xs) =
  if a == xa && b == xb || a == xb && b == xa then xc else getBudgetNodes a b xs

getBudgetsPath :: [(Int, Int, Int)] -> [Int] -> [Int]
getBudgetsPath _ [] = []
getBudgetsPath _ [_] = []
getBudgetsPath edges (a : b : xs) = getBudgetNodes a b edges : getBudgetsPath edges (b : xs)

isPossiblePath :: Int -> [(Int, Int, Int)] -> [Int] -> Bool
isPossiblePath _ _ [] = True
isPossiblePath budg edges path = sum (getBudgetsPath edges path) <= budg

dropRest :: [Int] -> [Int]
dropRest [] = []
dropRest (a : as) = if a == 88 then [a] else a : dropRest as

getPossiblePaths :: MapData -> Int -> [[Int]]
getPossiblePaths (MapData _ r s budg) _ =
  nextMove
  where
    nextMove = filter (elem 88) nextPossibleMoves
    nextPossibleMoves = filter (isPossiblePath budg edges) nextMoves
    nextMoves = map dropRest $ allPaths s edges []
    edges = extractRoads r

findNextMove :: MapData -> Int -> Int
findNextMove mdata ppos =
  case sortedPaths of
    [] -> startLocation mdata
    (a : _) -> if processedMove == ppos && elem ppos (critical (locations mdata)) then startLocation mdata else processedMove
      where
        processedMove = a !! 1
  where
    sortedPaths = sortBy (compare `on` length) paths
    paths = getPossiblePaths mdata ppos

launchAI :: Options -> IO ()
launchAI (Options f p) = do
  handle <- openFile f ReadMode
  contents <- hGetContents handle
  case decode contents :: Result MapData of
    Ok x -> print $ findNextMove x p
    x@(Error _) -> print x
