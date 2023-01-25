module CaesarTest exposing (..)

import Caesar exposing (..)
import Dict exposing (merge)
import Expect exposing (Expectation)
import Fuzz exposing (Fuzzer, int, list, string)
import Test exposing (..)


encodeTests : Test
encodeTests =
    describe "Encode tests"
        [ test "x -5> c" <| \_ -> 'c' |> Expect.equal (encode 5 'x')
        , test "T -7> A" <| \_ -> 'A' |> Expect.equal (encode 7 'T')
        ]


decodeTests : Test
decodeTests =
    describe "Decode tests"
        [ test "c -5> x" <| \_ -> 'x' |> Expect.equal (decode 5 'c')
        , test "A -7> T" <| \_ -> 'T' |> Expect.equal (decode 7 'A')
        ]


pythagorasTests : Test
pythagorasTests =
    describe "Pythagoras tests"
        [ test "Pythagoras - 3 4 5 Triangle" <| \_ -> True |> Expect.equal (isTriple 3 4 5)
        , test "Pythagoras - 3 4 6 Triangle" <| \_ -> False |> Expect.equal (isTriple 3 4 6)
        , test "Pythagoras - Negative Length" <| \_ -> False |> Expect.equal (isTriple 3 -3 6)
        , test "Pythagoras - Null Length" <| \_ -> False |> Expect.equal (isTriple 3 0 6)
        , test "Pythagoras - All Null Lengths" <| \_ -> False |> Expect.equal (isTriple 0 0 0)
        , test "Pythagoras - Leg 1 with Parameters 5 / 4" <| \_ -> 9 |> Expect.equal (leg1 5 4)
        , test "Pythagoras - Leg 2 with Parameters 5 / 4" <| \_ -> 40 |> Expect.equal (leg2 5 4)
        , test "Pythagoras - Hyp with Parameters 5 / 4" <| \_ -> 41 |> Expect.equal (hyp 5 4)
        , test "Pythagoras - Check with parameters found by Legs and Hyp" <| \_ -> True |> Expect.equal (isTriple 9 40 41)
        , test "Pythagoras - Check PythTriple with Tuple (5, 4)" <| \_ -> ( 9, 40, 41 ) |> Expect.equal (pythTriple ( 5, 4 ))
        , test "Pythagoras - Check PythTriple with (9, 40, 41) Triple from previous exercises" <| \_ -> True |> Expect.equal (isTripleTuple (pythTriple ( 5, 4 )))
        , test "Pythagoras - Check PythTriple with random Triple" <| \_ -> False |> Expect.equal (isTripleTuple (pythTriple ( 4, 4 )))
        ]


recodedUtilsFunctions : Test
recodedUtilsFunctions =
    describe "Recoded Utils Functions Tests"
        [ test "StringFilter - Basic Filter on String" <| \_ -> "HelloFontys" |> Expect.equal (myStringFilter Char.isAlpha "Hello, Fontys!")
        , test "StringFilter - Useless Filter" <| \_ -> "HelloFontys" |> Expect.equal (myStringFilter Char.isAlpha "HelloFontys")
        , test "ListFilter - Basic Filter on String" <| \_ -> [ 'H', 'e', 'l', 'l', 'o', 'F', 'o', 'n', 't', 'y', 's' ] |> Expect.equal (myListFilter Char.isAlpha [ 'H', 'e', 'l', 'l', 'o', ',', ' ', 'F', 'o', 'n', 't', 'y', 's', '!' ])
        , test "ListFilter - Useless Filter" <| \_ -> [ 'H', 'e', 'l', 'l', 'o', 'F', 'o', 'n', 't', 'y', 's' ] |> Expect.equal (myListFilter Char.isAlpha [ 'H', 'e', 'l', 'l', 'o', 'F', 'o', 'n', 't', 'y', 's' ])
        , test "StringMap - Decode on a String" <| \_ -> "HelloFontys" |> Expect.equal (myStringMap (decode 7) "OlssvMvuafz")
        , test "StringMap - Encode on a String" <| \_ -> "OlssvMvuafz" |> Expect.equal (myStringMap (encode 7) "HelloFontys")
        , test "ListMap - Decode on a String" <| \_ -> [ 'H', 'e', 'l', 'l', 'o', 'F', 'o', 'n', 't', 'y', 's' ] |> Expect.equal (myListMap (decode 7) [ 'O', 'l', 's', 's', 'v', 'M', 'v', 'u', 'a', 'f', 'z' ])
        , test "ListMap - Encode on a String" <| \_ -> [ 'O', 'l', 's', 's', 'v', 'M', 'v', 'u', 'a', 'f', 'z' ] |> Expect.equal (myListMap (encode 7) [ 'H', 'e', 'l', 'l', 'o', 'F', 'o', 'n', 't', 'y', 's' ])
        , test "ListStartsWith - Not Starting By Element" <| \_ -> False |> Expect.equal (myListStartsWith [ 'L', 'E', 'D' ] [ 'A', 'L', 'E', 'D', 'D' ])
        , test "ListStartsWith - Starting By Element" <| \_ -> True |> Expect.equal (myListStartsWith [ 'A', 'L', 'E', 'D' ] [ 'A', 'L', 'E', 'D', 'D' ])
        , test "ListStartsWith - No Element" <| \_ -> True |> Expect.equal (myListStartsWith [] [ 'A', 'L', 'E', 'D', 'D' ])
        , test "ListStartsWith - No Element In Comparison" <| \_ -> False |> Expect.equal (myListStartsWith [ 'A' ] [])
        , test "ListContains - Starting By Element" <| \_ -> True |> Expect.equal (myListContains [ 'A', 'L', 'E', 'D' ] [ 'A', 'L', 'E', 'D', 'D' ])
        , test "ListContains - Not starting By Element" <| \_ -> True |> Expect.equal (myListContains [ 'L', 'E', 'D' ] [ 'A', 'L', 'E', 'D', 'D' ])
        , test "ListContains - Not contained" <| \_ -> False |> Expect.equal (myListContains [ 'A', 'X', 'E', 'S' ] [ 'A', 'L', 'E', 'D', 'D' ])
        , test "StringContains - Starting By Element" <| \_ -> True |> Expect.equal (myStringContains "ALED" "ALEDD")
        , test "StringContains - Not Starting By Element" <| \_ -> True |> Expect.equal (myStringContains "LED" "ALEDD")
        , test "StringContains - Not contained" <| \_ -> False |> Expect.equal (myStringContains "AXES" "ALEDD")
        , test "InsertIntoList - Into Empty List" <| \_ -> [ 0 ] |> Expect.equal (insertIntoList 0 [] [])
        , test "InsertIntoList - One Element in Tiny List" <| \_ -> [ 1, 2, 3, 4, 5 ] |> Expect.equal (insertIntoList 4 [] [ 1, 2, 3, 5 ])
        , test "InsertIntoList - One Element in Long List" <| \_ -> [ 2, 7, 10, 14, 15, 18, 19, 22, 23, 34, 41, 42, 45, 45, 56, 57, 60, 64, 65, 65, 76, 79, 84, 86, 89, 91 ] |> Expect.equal (insertIntoList 45 [] [ 2, 7, 10, 14, 15, 18, 19, 22, 23, 34, 41, 42, 45, 56, 57, 60, 64, 65, 65, 76, 79, 84, 86, 89, 91 ])
        ]


normalizeTests : Test
normalizeTests =
    describe "Normalizing Strings Tests"
        [ test "Normalize - String with Spaces and Ponctuation" <| \_ -> "HelloWorld" |> Expect.equal (normalize "Hello World!!!!")
        , test "Normalize - String with Trailing Spaces and Ponctuation" <| \_ -> "HelloWorld" |> Expect.equal (normalize "Hello World!!!!!!!!,!,;,=:;,=:;,:;,=:;^`$^`$^ùù")
        , test "Normalize - String without Spaces and Ponctuation" <| \_ -> "HelloWorld" |> Expect.equal (normalize "HelloWorld")
        , test "Normalize - String with Beginning Trailing Spaces and Ponctuation" <| \_ -> "HelloWorld" |> Expect.equal (normalize "!!!!!!!!,!,;,=:;,=:;,:;,=:;^`$^`$^ùùHelloWorld")
        ]


cryptingTests : Test
cryptingTests =
    describe "Encrypting Strings Tests"
        [ test "Encrypt - Assignment Example n°1" <| \_ -> "OlssvMvuafz" |> Expect.equal (encrypt 7 (normalize "Hello, Fontys"))
        ]


decryptingTests : Test
decryptingTests =
    describe "Decrypting Strings Tests"
        [ test "Decrypt - Assignment Example n°2" <| \_ -> "HelloFontys" |> Expect.equal (decrypt 7 "OlssvMvuafz")
        ]


pythagorasTripleCheckingTests : Test
pythagorasTripleCheckingTests =
    describe "Pythagoras List Tests"
        [ test "Pythagoras Map - Assignment Example n°1" <| \_ -> [ ( 9, 40, 41 ), ( 3, 4, 5 ), ( 1176, 490, 1274 ) ] |> Expect.equal (pythTriplesMap [ ( 5, 4 ), ( 2, 1 ), ( 35, 7 ) ])
        , test "Pythagoras Recursive - Assignment Example n°2" <| \_ -> [ ( 9, 40, 41 ), ( 3, 4, 5 ), ( 1176, 490, 1274 ) ] |> Expect.equal (pythTriplesRec [ ( 5, 4 ), ( 2, 1 ), ( 35, 7 ) ])
        , test "Pythagoras List.filter - Assignment Example n°3" <| \_ -> [ ( 9, 40, 41 ), ( 3, 4, 5 ) ] |> Expect.equal (arePythTriplesFilter [ ( 1, 2, 3 ), ( 9, 40, 41 ), ( 3, 4, 5 ), ( 100, 2, 500 ) ])
        , test "Pythagoras Recursive Filter - Assignment Example n°4" <| \_ -> [ ( 9, 40, 41 ), ( 3, 4, 5 ) ] |> Expect.equal (arePythTriplesRec [ ( 1, 2, 3 ), ( 9, 40, 41 ), ( 3, 4, 5 ), ( 100, 2, 500 ) ])
        ]


creditCardNumberTests : Test
creditCardNumberTests =
    describe "Credit Card Validation Number Tests"
        [ test "Reverse List" <| \_ -> [ 1, 2, 3, 4, 5 ] |> Expect.equal (myListReverse [ 5, 4, 3, 2, 1 ])
        , test "Reverse Empty List" <| \_ -> [] |> Expect.equal (myListReverse [])
        , test "Undouble Number with no number > than 10" <| \_ -> [ 1, 2, 3, 4, 5 ] |> Expect.equal (undoubleNumber [ "1", "2", "3", "4", "5" ])
        , test "Undouble Number with one number > than 10" <| \_ -> [ 1, 0, 2, 3, 4, 5 ] |> Expect.equal (undoubleNumber [ "10", "2", "3", "4", "5" ])
        , test "Undouble Number with all numbers > than 10" <| \_ -> [ 1, 0, 2, 1, 3, 2, 4, 3, 5, 4 ] |> Expect.equal (undoubleNumber [ "10", "21", "32", "43", "54" ])
        , test "Double Values from Lists" <| \_ -> [ "1", "4", "3", "8", "5" ] |> Expect.equal (doubleValues 1 1 [ '1', '2', '3', '4', '5' ])
        , test "Double Value from Valid String Number" <| \_ -> "10" |> Expect.equal (doubleValue '5')
        , test "Double Value from Invalid String Number" <| \_ -> "0" |> Expect.equal (doubleValue 'a')
        , test "Sum all values from List" <| \_ -> 22 |> Expect.equal (myListSum [ 1, 2, 3, 4, 5, 6, 1 ])
        , test "Check Credit Card Number - Not Right Card Number" <| \_ -> False |> Expect.equal (checkCardNumberValue [ 1, 1, 6, 8, 2, 8, 1, 6, 8, 1, 6, 8, 1, 6, 8, 1, 6, 2, 2, 1, 8 ])
        , test "Tell if Card Number is Valid - Not Right Card Number" <| \_ -> False |> Expect.equal (isCardValid "4112888888881881")
        , test "Reverse List - Assignment Example n°1" <| \_ -> [ '1', '8', '8', '1', '8', '8', '8', '8', '8', '8', '8', '8', '2', '1', '0', '4' ] |> Expect.equal (myListReverse [ '4', '0', '1', '2', '8', '8', '8', '8', '8', '8', '8', '8', '1', '8', '8', '1' ])
        , test "Double Values - Assignment Example n°1" <| \_ -> [ "1", "16", "8", "2", "8", "16", "8", "16", "8", "16", "8", "16", "2", "2", "0", "8" ] |> Expect.equal (doubleValues 1 1 [ '1', '8', '8', '1', '8', '8', '8', '8', '8', '8', '8', '8', '2', '1', '0', '4' ])
        , test "Sum all values from List - Assignment Example n°1" <| \_ -> 90 |> Expect.equal (myListSum [ 1, 1, 6, 8, 2, 8, 1, 6, 8, 1, 6, 8, 1, 6, 8, 1, 6, 2, 2, 0, 8 ])
        , test "Check Credit Card Number - Assignment Example n°1" <| \_ -> True |> Expect.equal (checkCardNumberValue [ 1, 1, 6, 8, 2, 8, 1, 6, 8, 1, 6, 8, 1, 6, 8, 1, 6, 2, 2, 0, 8 ])
        , test "Tell if Card Number is Valid - Assignment Example n°1" <| \_ -> True |> Expect.equal (isCardValid "4012888888881881")
        , test "Empty List Valid Number Verification" <| \_ -> 0 |> Expect.equal (numValid [])
        , test "Tell if list with one card number is valid - Assignment Example n°1" <| \_ -> 1 |> Expect.equal (numValid [ "4012888888881881" ])
        , test "Tell if list with multiple card numbers are valids (All card numbers are valids)" <| \_ -> 3 |> Expect.equal (numValid [ "4012888888881881", "2222410740360010", "5577000055770004" ])
        , test "Tell if list with multiple card numbers are valids (Using invalid numbers)" <| \_ -> 3 |> Expect.equal (numValid [ "4012888888881881", "4112888888881881", "2222410740360010", "5577000055770004" ])
        ]


candidatesTests : Test
candidatesTests =
    describe "Candidates Function List Tests"
        [ test "Candidates - No Candidates" <| \_ -> [] |> Expect.equal (candidates [] "ALKJHGHJKLMKJHUKGYJFHVBJNKJLIOUYIGFJV")
        , test "Candidates - Candidates Not Found" <| \_ -> [] |> Expect.equal (candidates [ "JAITROPMANGE", "KROKODEALSURTWITTER" ] "LKJHKGBNKJLOIUYGHJBKIUYTFGHV")
        , test "Candidates - Assignment Example n°1" <| \_ -> [ ( 5, "YBBVYWXJJXUTHECUTQHOJEJXUCQN" ), ( 14, "PSSMPNOAAOLKYVTLKHYFAVAOLTHE" ), ( 21, "ILLFIGHTTHEDROMEDARYTOTHEMAX" ) ] |> Expect.equal (candidates [ "THE", "AND" ] "DGGADBCOOCZYMJHZYVMTOJOCZHVS")
        ]


msortTests : Test
msortTests =
    describe "Merge Sort Tests"
        [ test "Empty list" <| \_ -> [] |> Expect.equal (msort [])
        , test "One element list" <| \_ -> [ 0 ] |> Expect.equal (msort [ 0 ])
        , test "Two element list sorted" <| \_ -> [ 0, 1 ] |> Expect.equal (msort [ 0, 1 ])
        , test "Two element list not sorted" <| \_ -> [ 0, 1 ] |> Expect.equal (msort [ 1, 0 ])
        , test "Large list not sorted n°1" <| \_ -> List.range 1 100 |> Expect.equal (msort [ 31, 55, 30, 37, 91, 89, 41, 54, 13, 48, 78, 57, 33, 82, 70, 21, 20, 93, 12, 46, 73, 63, 8, 22, 80, 29, 2, 58, 42, 10, 69, 47, 9, 64, 62, 90, 61, 26, 97, 87, 60, 27, 39, 7, 40, 49, 53, 15, 84, 95, 65, 3, 74, 16, 18, 83, 67, 19, 96, 28, 92, 79, 36, 45, 44, 23, 86, 59, 68, 38, 1, 17, 94, 35, 24, 50, 66, 5, 52, 25, 6, 34, 4, 51, 98, 56, 11, 99, 77, 75, 72, 76, 32, 71, 14, 100, 88, 85, 43, 81 ])
        , test "Large list not sorted n°2" <| \_ -> [ 29, 33, 35, 36, 40, 55, 73, 80, 84, 86, 87, 104, 106, 113, 116, 120, 126, 133, 139, 140, 152, 153, 162, 165, 165, 171, 184, 185, 188, 189, 193, 198, 203, 219, 222, 246, 253, 261, 266, 274, 296, 305, 305, 308, 313, 319, 319, 321, 334, 344, 352, 357, 360, 364, 368, 369, 373, 382, 383, 398, 406, 415, 422, 422, 427, 428, 429, 438, 441, 458, 469, 474, 482, 483, 486, 489, 492, 498, 499, 509, 513, 514, 519, 522, 525, 543, 561, 562, 564, 580, 585, 588, 590, 602, 624, 634, 638, 640, 645, 649, 651, 653, 657, 658, 666, 672, 675, 695, 695, 705, 708, 711, 714, 732, 738, 750, 755, 769, 770, 775, 780, 799, 800, 805, 820, 842, 847, 860, 860, 863, 873, 876, 886, 889, 892, 893, 900, 908, 915, 925, 931, 946, 947, 950, 961, 961, 979, 983, 990, 992 ] |> Expect.equal (msort [ 188, 352, 126, 33, 84, 562, 373, 645, 925, 319, 638, 775, 36, 946, 73, 711, 152, 360, 474, 429, 184, 820, 406, 651, 893, 519, 364, 602, 321, 193, 162, 120, 113, 427, 499, 368, 799, 873, 369, 441, 979, 469, 140, 357, 705, 590, 950, 649, 313, 253, 961, 666, 564, 961, 863, 104, 525, 133, 334, 800, 695, 892, 860, 438, 588, 483, 55, 675, 139, 992, 308, 246, 458, 585, 415, 755, 489, 486, 305, 153, 513, 947, 805, 634, 198, 185, 889, 382, 657, 876, 708, 658, 714, 189, 842, 672, 219, 908, 319, 106, 203, 860, 40, 165, 750, 422, 428, 522, 931, 171, 653, 274, 383, 915, 344, 116, 990, 847, 296, 738, 695, 983, 770, 87, 80, 732, 769, 509, 261, 780, 498, 482, 492, 398, 900, 165, 640, 86, 561, 543, 624, 266, 580, 305, 35, 514, 886, 29, 222, 422 ])
        , test "Large list not sorted n°3" <| \_ -> [ 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 9, 9, 10, 10, 10 ] |> Expect.equal (msort [ 6, 8, 2, 9, 5, 2, 8, 2, 6, 5, 7, 5, 7, 2, 5, 5, 6, 8, 6, 6, 3, 8, 7, 5, 1, 7, 1, 3, 4, 3, 2, 6, 1, 3, 1, 10, 9, 2, 2, 10, 2, 3, 2, 10, 8, 8, 3, 5, 5, 8 ])
        ]


mergeListTests : Test
mergeListTests =
    describe "Merge List Tests"
        [ test "Merge List - Merge Empty List to Empty List" <| \_ -> [] |> Expect.equal (mergeList [] [])
        , test "Merge List - Merge Empty List to List" <| \_ -> [ 1, 2, 3, 4, 5 ] |> Expect.equal (mergeList [] [ 1, 2, 3, 4, 5 ])
        , test "Merge List - Merge List to Empty List" <| \_ -> [ 1, 2, 3, 4, 5 ] |> Expect.equal (mergeList [ 1, 2, 3, 4, 5 ] [])
        , test "Merge List - Merge List to List" <| \_ -> [ 1, 2, 3, 4, 5 ] |> Expect.equal (mergeList [ 1, 2, 3 ] [ 4, 5 ])
        , test "Merge List - Merge Big List to Big List" <| \_ -> [ 29, 33, 35, 36, 40, 55, 73, 80, 84, 86, 87, 104, 106, 113, 116, 120, 126, 133, 139, 140, 152, 153, 162, 165, 165, 171, 184, 185, 188, 189, 193, 198, 203, 219, 222, 246, 253, 261, 266, 274, 296, 305, 305, 308, 313, 319, 319, 321, 334, 344, 352, 357, 360, 364, 368, 369, 373, 382, 383, 398, 406, 415, 422, 422, 427, 428, 429, 438, 441, 458, 469, 474, 482, 483, 486, 489, 492, 498, 499, 509, 513, 514, 519, 522, 525, 543, 561, 562, 564, 580, 585, 588, 590, 602, 624, 634, 638, 640, 645, 649, 651, 653, 657, 658, 666, 672, 675, 695, 695, 705, 708, 711, 714, 732, 738, 750, 755, 769, 770, 775, 780, 799, 800, 805, 820, 842, 847, 860, 860, 863, 873, 876, 886, 889, 892, 893, 900, 908, 915, 925, 931, 946, 947, 950, 961, 961, 979, 983, 990, 992 ] |> Expect.equal (mergeList [ 29, 33, 35, 36, 40, 55, 73, 80, 84, 86, 87, 104, 106, 113, 116, 120, 126, 133, 139 ] [ 140, 152, 153, 162, 165, 165, 171, 184, 185, 188, 189, 193, 198, 203, 219, 222, 246, 253, 261, 266, 274, 296, 305, 305, 308, 313, 319, 319, 321, 334, 344, 352, 357, 360, 364, 368, 369, 373, 382, 383, 398, 406, 415, 422, 422, 427, 428, 429, 438, 441, 458, 469, 474, 482, 483, 486, 489, 492, 498, 499, 509, 513, 514, 519, 522, 525, 543, 561, 562, 564, 580, 585, 588, 590, 602, 624, 634, 638, 640, 645, 649, 651, 653, 657, 658, 666, 672, 675, 695, 695, 705, 708, 711, 714, 732, 738, 750, 755, 769, 770, 775, 780, 799, 800, 805, 820, 842, 847, 860, 860, 863, 873, 876, 886, 889, 892, 893, 900, 908, 915, 925, 931, 946, 947, 950, 961, 961, 979, 983, 990, 992 ])
        ]


functionPrintTests : Test
functionPrintTests =
    describe "Function print Tests"
        [ test "Subject test" <|
            \_ ->
                "(((3 + x) * (x - (x ^ 5))) + 2)"
                    |> Expect.equal
                        (print
                            (Plus (Mult (Plus (Const 3) X) (Minus X (Poly X 5))) (Const 2))
                        )
        , test "Subject graph test" <|
            \_ ->
                "(((((x / 5) - 1) ^ 4) - (((x / -2) + 2) ^ 2)) + 6)"
                    |> Expect.equal
                        (print
                            (Plus (Minus (Poly (Minus (Div X (Const 5)) (Const 1)) 4) (Poly (Plus (Div X (Const -2)) (Const 2)) 2)) (Const 6))
                        )
        ]


evalTests : Test
evalTests =
    describe "Eval Tests"
        [ test "Subject test" <|
            \_ ->
                -148
                    |> Expect.equal
                        (eval
                            2
                            (Plus (Mult (Plus (Const 3) X) (Minus X (Poly X 5))) (Const 2))
                        )
        ]


graphTests : Test
graphTests =
    describe "Graph Tests"
        [ test "Subject test" <|
            \_ ->
                [ "********************"
                , "********************"
                , "********************"
                , "******************--"
                , "**************------"
                , "***********---------"
                , "**********----------"
                , "**********----------"
                , "**********----------"
                , "***********---------"
                , "*************-------"
                , "**************------"
                , "***************-----"
                , "***************-----"
                , "****************----"
                , "***************-----"
                , "***************-----"
                , "*************-------"
                , "************--------"
                , "**********----------"
                , "********------------"
                , "******--------------"
                , "****----------------"
                , "***-----------------"
                , "**------------------"
                , "**------------------"
                , "****----------------"
                , "*******-------------"
                , "************--------"
                , "********************"
                ]
                    |> Expect.equal
                        (graph
                            (Plus (Minus (Poly (Minus (Div X (Const 5)) (Const 1)) 4) (Poly (Plus (Div X (Const -2)) (Const 2)) 2)) (Const 6))
                            -10
                            20
                            -10
                            10
                        )
        ]


repeatUntilTests : Test
repeatUntilTests =
    describe "Repeat Until Tests"
        [ test "Repeat Until - Assignment Example n°1" <| \_ -> 112 |> Expect.equal (repeatUntil above100 ((*) 2) 7)
        , test "Repeat Until - Assignment Example n°2" <| \_ -> 101 |> Expect.equal (repeatUntil above100 ((+) 1) 42)
        , test "Repeat Until - Repeat with reverse square function" <| \_ -> 65536 |> Expect.equal (repeatUntil above100 ((^) 2) 2)
        , test "Repeat Until - Repeat with square function" <| \_ -> 256 |> Expect.equal (repeatUntil above100 (\x -> x ^ 2) 2)
        , test "Repeat Until - Repeat with square function with negative number" <| \_ -> 65536 |> Expect.equal (repeatUntil above100 ((^) -2) 2)
        , test "Repeat Until - Repeat with Divisions" <| \_ -> 10 |> Expect.equal (repeatUntil (\x -> x < 100) (\x -> x // 10) 10000000)
        , test "Repeat Until - myCollatz Implementation with 19" <| \_ -> [ 1, 2, 4, 8, 16, 5, 10, 20, 40, 13, 26, 52, 17, 34, 11, 22, 44, 88, 29, 58, 19 ] |> Expect.equal (repeatUntil (\x -> List.head x == Just 1) myCollatz [ 19 ])
        , test "Repeat Until - myCollatz Implementation with 27" <| \_ -> [ 1, 2, 4, 8, 16, 5, 10, 20, 40, 80, 160, 53, 106, 35, 70, 23, 46, 92, 184, 61, 122, 244, 488, 976, 325, 650, 1300, 433, 866, 1732, 577, 1154, 2308, 4616, 9232, 3077, 6154, 2051, 4102, 1367, 2734, 911, 1822, 3644, 7288, 2429, 4858, 1619, 3238, 1079, 2158, 719, 1438, 479, 958, 319, 638, 1276, 425, 850, 283, 566, 1132, 377, 754, 251, 502, 167, 334, 668, 1336, 445, 890, 1780, 593, 1186, 395, 790, 263, 526, 175, 350, 700, 233, 466, 155, 310, 103, 206, 412, 137, 274, 91, 182, 364, 121, 242, 484, 161, 322, 107, 214, 71, 142, 47, 94, 31, 62, 124, 41, 82, 27 ] |> Expect.equal (repeatUntil (\x -> List.head x == Just 1) myCollatz [ 27 ])
        , test "Repeat Until - myCollatz Implementation with 42" <| \_ -> [ 1, 2, 4, 8, 16, 32, 64, 21, 42 ] |> Expect.equal (repeatUntil (\x -> List.head x == Just 1) myCollatz [ 42 ])
        , test "Repeat Until - myCollatz Implementation with 31" <| \_ -> [ 1, 2, 4, 8, 16, 5, 10, 20, 40, 80, 160, 53, 106, 35, 70, 23, 46, 92, 184, 61, 122, 244, 488, 976, 325, 650, 1300, 433, 866, 1732, 577, 1154, 2308, 4616, 9232, 3077, 6154, 2051, 4102, 1367, 2734, 911, 1822, 3644, 7288, 2429, 4858, 1619, 3238, 1079, 2158, 719, 1438, 479, 958, 319, 638, 1276, 425, 850, 283, 566, 1132, 377, 754, 251, 502, 167, 334, 668, 1336, 445, 890, 1780, 593, 1186, 395, 790, 263, 526, 175, 350, 700, 233, 466, 155, 310, 103, 206, 412, 137, 274, 91, 182, 364, 121, 242, 484, 161, 322, 107, 214, 71, 142, 47, 94, 31 ] |> Expect.equal (repeatUntil (\x -> List.head x == Just 1) myCollatz [ 31 ])
        ]


derivativeTests : Test
derivativeTests =
    describe "Derivative Expression Tests"
        [ test "Basic X Expression" <| \_ -> "(0 + ((4 * 1) + (0 * x)))" |> Expect.equal (print (derivative (Plus (Const 3) (Mult (Const 4) X))))
        , test "Simple Number" <| \_ -> "0" |> Expect.equal (print (derivative (Const 4)))
        , test "Multiple Operands Expression" <| \_ -> "(0 + (0 - ((((2 * 2) * 0) - (((2 * 0) + (0 * 2)) * 4)) / ((2 * 2) ^ 2))))" |> Expect.equal (print (derivative (Plus (Const 3) (Minus (Const 2) (Div (Const 4) (Mult (Const 2) (Const 2)))))))
        ]


simplifyTests : Test
simplifyTests =
    describe "Simplify Expression Tests"
        [ test "Basic X Expression" <| \_ -> "4" |> Expect.equal (print (simplify (derivative (Plus (Const 3) (Mult (Const 4) X)))))
        , test "Simple Number Simplification" <| \_ -> "0" |> Expect.equal (print (simplify (derivative (Const 4))))
        , test "Multiple Operands Expression" <| \_ -> "(0 - (0 / 16))" |> Expect.equal (print (simplify (derivative (Plus (Const 3) (Minus (Const 2) (Div (Const 4) (Mult (Const 2) (Const 2))))))))
        , test "Multiple Operands Expression n°2" <| \_ -> "(4 + (x + x))" |> Expect.equal (print (simplify (derivative (Plus (Mult (Const 4) X) (Mult X X)))))
        , test "Multiple Operands Expression n°3" <| \_ -> "(4 + ((x + (x + x)) + (x + x)))" |> Expect.equal (print (simplify (derivative (Plus (Mult (Const 4) X) (Mult X (Mult X X))))))
        ]
