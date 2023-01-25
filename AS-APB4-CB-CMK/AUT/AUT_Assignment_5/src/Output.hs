module Output 
    (
        generateFinalStates,
        generateFileStart,
        datumToGraphviz,
        generateEntryPoint,
        connectEntryPoint,
        generateConnections
    )
    where


generateFileStart :: String
generateFileStart =
    "digraph generatedAutomaton {\n\trankdir=LR\n\tnode [shape = circle, style = filled, fillcolor = white, fontname = Arial]\n\tedge [fontname = Arial]\n"

-------------------------------------------------------

generateEntryPoint :: String
generateEntryPoint = "\t\"\" [style = filled, fontcolor = white, color = white]\n"

-------------------------------------------------------

connectEntryPoint :: String -> String
connectEntryPoint initialState = "\t\"\" -> \"" ++ initialState ++ "\"\n"

-------------------------------------------------------

generateFinalStates :: [String] -> String
generateFinalStates [] = ""
generateFinalStates (x:xs) = "\t\"" ++ x ++ "\" [shape=doublecircle]\n" ++ generateFinalStates xs

-------------------------------------------------------

generateConnections :: [(String, String, String)] -> String
generateConnections [] = "}"
generateConnections ((a, b, trans):xs) =
    "\t\"" ++ a ++ "\" -> \"" ++ b ++ "\" [label=\"" ++ trans ++ "\"]\n" ++ generateConnections xs

-------------------------------------------------------

datumToGraphviz :: String -> [String] -> [(String, String, String)] -> String
datumToGraphviz is fs connections = generateFileStart ++ generateEntryPoint ++ generateFinalStates fs ++ connectEntryPoint is ++ generateConnections connections
