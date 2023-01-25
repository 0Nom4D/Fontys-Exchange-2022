import Output
import Test.Framework ( Test, testGroup, defaultMain )
import Test.Framework.Providers.HUnit ( testCase )
import Test.HUnit ( assertEqual )

main :: IO ()
main = defaultMain [outputTests]

-- Output Module Specs

outputTests :: Test
outputTests = testGroup "Output Creation Functions Tests" [
    test_start_file, test_empty_final_states, test_final_states, test_empty_datum_list,
    test_one_datum_list, test_two_datum_list, test_automaton_file_test]

test_start_file :: Test
test_start_file = testCase "Basic Start of File" $ assertEqual "" output value
    where
        output = "digraph generatedAutomaton {\n\trankdir=LR\n\tnode [shape = circle, style = filled, fillcolor = white, fontname = Arial]\n\tedge [fontname = Arial]\n"
        value = generateFileStart

test_empty_final_states :: Test
test_empty_final_states = testCase "Empty Final States" $ assertEqual "" output value
    where
        output = ""
        value = generateFinalStates []

test_final_states :: Test
test_final_states = testCase "2 Final States" $ assertEqual "" output value
    where
        output = "\t\"1000\" [shape=doublecircle]\n\t\"1001\" [shape=doublecircle]\n"
        value = generateFinalStates ["1000", "1001"]

test_empty_datum_list :: Test
test_empty_datum_list = testCase "Empty Datum List States" $ assertEqual "" output value
    where
        output = "}\n"
        value = generateConnections []

test_one_datum_list :: Test
test_one_datum_list = testCase "List of one Datum" $ assertEqual "" output value
    where
        output = "\t\"1000\" -> \"1001\" [label=\"a\"]\n}\n"
        value = generateConnections [("1000", "1001", "a")]

test_two_datum_list :: Test
test_two_datum_list = testCase "List of 2 Datum" $ assertEqual "" output value
    where
        output = "\t\"1000\" -> \"1001\" [label=\"a\"]\n\t\"1001\" -> \"1000\" [label=\"b\"]\n}\n"
        value = generateConnections [("1000", "1001", "a"), ("1001", "1000", "b")]

test_automaton_file_test :: Test
test_automaton_file_test = testCase "Generate full Automaton File" $ assertEqual "" output value
    where
        output = "digraph generatedAutomaton {\n\trankdir=LR\n\tnode [shape = circle, style = filled, fillcolor = white, fontname = Arial]\n\tedge [fontname = Arial]\n\t\"\" [style = filled, fontcolor = white, color = white]\n\t\"1001\" [shape=doublecircle]\n\t\"\" -> \"1000\"\n\t\"1000\" -> \"1001\" [label=\"a\"]\n}\n"
        value = generateFileStart ++ generateEntryPoint ++ generateFinalStates ["1001"] ++ connectEntryPoint "1000" ++ generateConnections [("1000", "1001", "a")]
