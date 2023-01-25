module Lib
    ( nfaToGraphviz
    ) where

import Output ( datumToGraphviz )

import Parsing
import Jaarse

isFunction :: String -> Datum -> Bool
isFunction wantedName (List ((Atom "define-fun"):(Atom name):_)) =
  name == wantedName
isFunction _ _ = error "Not a function"

getFunction :: Datum -> String -> Datum
getFunction (List (_:List x: _)) name = head $ filter (isFunction name) x
getFunction _ name = error $ "Couldn't get function " ++ name

getFunctionBody :: Datum -> Datum
getFunctionBody (List (_:_:_:_:body:_)) = body
--               define name args return
getFunctionBody _ = error "Couldn't get function body"

getConnections :: Datum -> [(String, String, String)]
getConnections (List (_:List (_:List (_:_:Atom start:_):List (_:_:Atom end:_):List (_:_:(DString transition):_):_):_:rest:_)) = (start, end, transition) : getConnections rest
--                    ite     and     = x!0                   = x!1                 = x!2                          true
getConnections _ = []

getFinalStates :: Datum -> [String]
getFinalStates (List (_:List (_:_:Atom x:_):_:rest:_)) = x : getFinalStates rest
--                   ite      = x!0         true
getFinalStates _ = []

getInitialState :: Datum -> String
getInitialState (Atom x) = x
getInitialState _ = error "Couldn't get initial state"

nfaToGraphviz :: String -> Maybe String
nfaToGraphviz a =
  case runParser list a of
    Nothing -> Nothing
    Just (a1, "") -> Just $ datumToGraphviz initialState finalStates connections
      where
        connections = getConnections $ getFunctionBody $ getFunction a1 "A"
        finalStates = getFinalStates $ getFunctionBody $ getFunction a1 "F"
        initialState = getInitialState $ getFunctionBody $ getFunction a1 "InitState"
    Just _ -> Nothing
