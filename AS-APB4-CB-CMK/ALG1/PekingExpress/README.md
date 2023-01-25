# Assignment 4: Peking Express

*This assignments has been done with [Alexandre FLION](https://github.com/huntears) from EPITECH Toulouse during our Fontys Exchange.*

The goal of this assignment is to make an AI playing a Peking Express game and choosing the fastest path to node 88.

This project has been done using Python, for the graphical interface, and Haskell for the AI.

## How to launch

This project is entirely launched by the front end. In order to launch it, you'll need to go to the front [folder](./front/).

Then, you'll need to run the following command:

```txt
$> make re
```

After that, you'll be able to enter an input which is basically the number of the node, you want to go.

If the node you want to go is not a neighbour of the node where you are, there will be an error.

If you don't have enough budget to go to any node, you will have to play the same node as your player position as a 'wait' command.

When you enter a valid neighbour, a graph will be displayed using networkx showing:

- In green, the node where the player is.
- In black, the node where both the player and the ai are.
- In red, the node where the AI is.

If you want to make the AI play first, you'll need to change in the file 'main.py' the line 27 by:

```py
    return drawer.launchGame(False)
```

## Graphic Interface

The game also has a graphic interface made with python and networkx.

This code has a lot of parts such as a Graph and Node implementation, in Python, and game logic using loops and winning / draw and losing conditions.

```py
from os import close

from sources.characters import Player, AI, CharacterType, Characters
from subprocess import check_output
from enum import IntEnum

from json import dump

import matplotlib.pyplot as plt
import networkx as nx


class Vertex:
    def __init__(self, index, critical=False):
        self.index = index
        self.critical = critical
        self.neighbours = {}

    def add_neighbour(self, vertex, weight=0):
        self.neighbours[vertex] = weight

    def remove_neighbour(self, vertex):
        del self.neighbours[vertex]

    def get_neighbours(self):
        return list(self.neighbours.keys())

    def weight(self, vertex):
        return self.neighbours[vertex]

    def set_critical(self, critical):
        self.critical = critical


class PEGraph:
    def __init__(self):
        self.vertices = {}
        self.num_vertices = 0

    def add_edge(self, u: int, v: int, weight: int):
        added_vertices = 0
        if u not in self.vertices:
            self.vertices[u] = Vertex(u)
            added_vertices += 1
        if v not in self.vertices:
            self.vertices[v] = Vertex(v)
            added_vertices += 1
        self.vertices[u].add_neighbour(v, weight)
        self.vertices[v].add_neighbour(u, weight)
        self.num_vertices += added_vertices

    def get_vertices(self):
        return self.vertices

    def get_vertex(self, u: int):
        return self.vertices[u] if u in self.vertices else None

    def update_critical(self, u: int, critical=True):
        vertex = self.get_vertex(u)
        vertex.set_critical(critical)


class GameState(IntEnum):
    VICTORY = 1
    DRAW = 0
    DEFEAT = -1


def createGraph(options):
    g = PEGraph()

    for i in range(len(options['Roads']['a'])):
        g.add_edge(options['Roads']['a'][i], options['Roads']['b'][i], options['Roads']['price'][i])
    for i in range(len(options['Locations']['critical'])):
        g.update_critical(options['Locations']['critical'][i], True)
    return g


class GraphDrawer:
    def __init__(self, options):
        self.graph = createGraph(options)

        self.drawing_options = options
        self.ai = AI(options['StartLocation'], options['Budget'])
        self.player = Player(options['StartLocation'], 1)
        self.vertices = self.getUniqueVertices()

    def getUniqueVertices(self):
        vertices = []
        sample = self.drawing_options['Roads']['a'] + self.drawing_options['Roads']['b']

        for v in sample:
            if v not in vertices:
                vertices.append(v)
        return vertices

    def drawGraph(self):
        G = nx.Graph()

        color_map = [None for i in range(len(self.vertices))]
        for index, vertex in enumerate(self.vertices):
            if vertex == self.player.position and vertex == self.ai.position:
                color_map[index] = 'black'
            elif vertex == self.player.position:
                color_map[index] = 'green'
            elif vertex == self.ai.position:
                color_map[index] = 'red'
            else:
                color_map[index] = 'blue'
        for i in range(len(self.drawing_options['Roads']['a'])):
            G.add_edge(
                self.drawing_options['Roads']['a'][i],
                self.drawing_options['Roads']['b'][i],
                weight=self.drawing_options['Roads']['price'][i]
            )
        pos = nx.spring_layout(G)
        nx.draw_networkx(G, pos, font_color="whitesmoke")
        labels = nx.get_edge_attributes(G, 'weight')
        nx.draw_networkx_nodes(G, pos, nodelist=self.vertices, node_color=color_map)
        nx.draw_networkx_edge_labels(G, pos, edge_labels=labels)

    def getGameResult(self) -> int:
        if self.player.position != 88 and self.ai.position == 88:
            print('AI won!')
            return GameState.DEFEAT
        elif self.player.position == 88 and self.ai.position != 88:
            print('Player won!')
            return GameState.VICTORY
        print('Player and AI draw!')
        return GameState.DRAW

    def updateCharacterPosition(self, c: Characters, destination: int):
        fromPosition = self.graph.get_vertex(c.position)
        weightFromPosition = fromPosition.weight(destination)
        c.removeBudget(weightFromPosition)
        c.setPosition(destination)

    def playAITurn(self):
        ai_data = self.drawing_options
        ai_data['StartLocation'] = self.ai.position
        ai_data['Budget'] = self.ai.budget

        with open("ai_data.json", 'w') as write:
            dump(ai_data, write)
        stdout = check_output(['../ai/.stack-work/dist/x86_64-osx/Cabal-3.4.1.0/build/ai-exe/ai-exe', '-f', 'ai_data.json', '-p', f'{self.player.position}'])
        dest = int(stdout)
        if dest != self.ai.position:
            self.updateCharacterPosition(self.ai, dest)
        self.drawGraph()
        plt.show()

    def playPlayersTurn(self):
        dest = None
        while dest is None:
            input_value = int(input('Where do you want to go? '))
            if input_value not in self.vertices:
                print("Destination doesn't exists.")
                continue
            dest = int(input_value)
            if self.graph.get_vertex(self.player.position).weight(dest) > self.player.budget:
                print(f'Not enough budget to go to node {dest}.')
                dest = None
                continue
            elif self.graph.get_vertex(dest).critical and self.ai.position == dest or dest not in self.graph.get_vertex(self.player.position).get_neighbours():
                print('Invalid move.')
                dest = None
                continue
        if dest != self.player.position:
            self.updateCharacterPosition(self.player, dest)
        self.drawGraph()
        plt.show()

    def launchGame(self, userFirst: bool) -> int:
        while (self.player.position != 88 and self.ai.position != 88) or (self.player.budget == 0 or self.player.budget == 0):
            aiPlayed = playerPlayed = False
            if userFirst:
                self.playPlayersTurn()
                playerPlayed = True
            else:
                self.playAITurn()
                aiPlayed = True
            if playerPlayed:
                self.playAITurn()
            elif aiPlayed:
                self.playPlayersTurn()
        return self.getGameResult()
```

## AI

The AI is made with Haskell. The AI can't loose if it plays first because it computes every possible outcomes and choose the best one.

**Don't be scared if the AI takes a lot of time to proceed, the algotihm behind it is not the fastest.**

```hs
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

```

The AI is a brute-force AI. On the file game17_m.json, the AI will take approximatively 30 seconds to get the next move.

The AI generates all branches possible and takes the fastest branch. Its complexity is basically O(n!).
