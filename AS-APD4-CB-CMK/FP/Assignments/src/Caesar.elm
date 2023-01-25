module Caesar exposing (..)

import Char exposing (fromCode, isAlpha, isLower, toCode)
import Html exposing (a)
import List exposing (..)



-- Week 1


upperShift : Int
upperShift =
    toCode 'A'


lowerShift : Int
lowerShift =
    toCode 'a'


tmpFunc : (Int -> Int) -> Char -> Int -> Char
tmpFunc f a b =
    fromCode <| (\x -> x + b) <| modBy 26 <| f <| (\x -> x - b) <| toCode a


applyToChar : (Int -> Int) -> Char -> Char
applyToChar f a =
    if isLower a then
        tmpFunc f a lowerShift

    else
        tmpFunc f a upperShift


encode : Int -> Char -> Char
encode a b =
    applyToChar (\x -> x + a) b


decode : Int -> Char -> Char
decode a b =
    applyToChar (\x -> x - a) b



-- Pythagoras Assignments


sqr : Int -> Int
sqr x =
    x ^ 2


computesPythagoras : Int -> Int -> Int
computesPythagoras x y =
    sqr x + sqr y


isTriple : Int -> Int -> Int -> Bool
isTriple x y z =
    if x <= 0 || y <= 0 || z <= 0 then
        False

    else if computesPythagoras x y == sqr z then
        True

    else
        False


leg1 : Int -> Int -> Int
leg1 x y =
    sqr x - sqr y


leg2 : Int -> Int -> Int
leg2 x y =
    2 * x * y


hyp : Int -> Int -> Int
hyp x y =
    sqr x + sqr y


pythTriple : ( Int, Int ) -> ( Int, Int, Int )
pythTriple ( x, y ) =
    ( leg1 x y, leg2 x y, hyp x y )


isTripleTuple : ( Int, Int, Int ) -> Bool
isTripleTuple ( x, y, z ) =
    isTriple x y z



-- Week 2


mapStringToList : (List Char -> List Char) -> String -> String
mapStringToList f s =
    String.fromList <| f <| String.toList s


myStringMap : (Char -> Char) -> String -> String
myStringMap f =
    mapStringToList (myListMap f)


myStringFilter : (Char -> Bool) -> String -> String
myStringFilter f =
    mapStringToList (myListFilter f)


myListMap : (a -> b) -> List a -> List b
myListMap f a =
    case a of
        [] ->
            []

        x :: xs ->
            f x :: myListMap f xs


myListFilter : (a -> Bool) -> List a -> List a
myListFilter f a =
    case a of
        [] ->
            []

        x :: xs ->
            if f x then
                x :: myListFilter f xs

            else
                myListFilter f xs


normalize : String -> String
normalize =
    myStringFilter isAlpha


encrypt : Int -> String -> String
encrypt n =
    myStringMap (encode n)


decrypt : Int -> String -> String
decrypt n =
    myStringMap (decode n)


pythTriplesMap : List ( Int, Int ) -> List ( Int, Int, Int )
pythTriplesMap =
    myListMap pythTriple


pythTriplesRec : List ( Int, Int ) -> List ( Int, Int, Int )
pythTriplesRec xs =
    case xs of
        [] ->
            []

        x :: xss ->
            pythTriple x :: pythTriplesRec xss


arePythTriplesFilter : List ( Int, Int, Int ) -> List ( Int, Int, Int )
arePythTriplesFilter =
    myListFilter isTripleTuple


arePythTriplesRec : List ( Int, Int, Int ) -> List ( Int, Int, Int )
arePythTriplesRec xs =
    case xs of
        [] ->
            []

        x :: xss ->
            if isTripleTuple x == True then
                x :: arePythTriplesRec xss

            else
                arePythTriplesRec xss



-- Week 3


myListStartsWith : List a -> List a -> Bool
myListStartsWith a b =
    case ( a, b ) of
        ( [], _ ) ->
            True

        ( _, [] ) ->
            False

        ( x :: xs, y :: ys ) ->
            if x == y then
                myListStartsWith xs ys

            else
                False


myListContains : List a -> List a -> Bool
myListContains a b =
    if myListStartsWith a b then
        True

    else
        case b of
            [] ->
                False

            _ :: xs ->
                myListContains a xs


myStringContains : String -> String -> Bool
myStringContains a b =
    -- Check if this can be simplified
    myListContains (String.toList a) (String.toList b)


candidates : List String -> String -> List ( Int, String )
candidates a s =
    myListFilter (\x -> List.foldr (||) False (myListMap (\y -> myStringContains y (Tuple.second x)) a)) <| myListMap (\x -> ( x, decrypt x s )) (List.range 0 25)


doubleValue : Char -> String
doubleValue n =
    String.fromInt (convertCharToInt n * 2)


doubleValues : Int -> Int -> List Char -> List String
doubleValues n it list =
    case list of
        [] ->
            []

        x :: xs ->
            case it of
                0 ->
                    doubleValue x :: doubleValues n n xs

                _ ->
                    String.fromChar x :: doubleValues n (it - 1) xs


myListReverse : List a -> List a
myListReverse xs =
    case xs of
        [] ->
            []

        x :: xss ->
            myListReverse xss ++ [ x ]


myListSum : List Int -> Int
myListSum =
    List.foldl (+) 0


convertCharToInt : Char -> Int
convertCharToInt nb =
    Maybe.withDefault 0 (String.toInt (String.fromChar nb))


convertStringToInt : String -> Int
convertStringToInt nb =
    Maybe.withDefault 0 (String.toInt nb)


undoubleNumber : List String -> List Int
undoubleNumber lst =
    case lst of
        [] ->
            []

        x :: xs ->
            case String.toList x of
                [] ->
                    convertStringToInt x :: undoubleNumber xs

                x1 :: xs1 ->
                    if xs1 == [] then
                        convertCharToInt x1 :: undoubleNumber xs

                    else
                        convertCharToInt x1 :: undoubleNumber (String.concat (myListMap String.fromChar xs1) :: xs)


checkCardNumberValue : List Int -> Bool
checkCardNumberValue lst =
    if modBy 10 (myListSum lst) > 0 then
        False

    else
        True


isCardValid : String -> Bool
isCardValid lst =
    checkCardNumberValue <| undoubleNumber <| doubleValues 1 1 <| myListReverse (String.toList lst)


numValid : List String -> Int
numValid card_nbs =
    List.foldl
        (\x a ->
            if x then
                a + 1

            else
                a
        )
        0
    <|
        myListMap isCardValid card_nbs



-- Week 4


insertIntoList : comparable -> List comparable -> List comparable -> List comparable
insertIntoList x a b =
    case b of
        [] ->
            a ++ [ x ]

        y :: ys ->
            if x <= y then
                a ++ x :: b

            else
                insertIntoList x (a ++ [ y ]) ys


mergeList : List comparable -> List comparable -> List comparable
mergeList a b =
    case a of
        [] ->
            b

        x :: xs ->
            mergeList xs <| insertIntoList x [] b


msort : List comparable -> List comparable
msort a =
    case a of
        [] ->
            []

        x :: [] ->
            [ x ]

        _ ->
            let
                midPoint =
                    List.length a // 2

                firstPart =
                    List.take midPoint a

                secondPart =
                    List.drop midPoint a
            in
            mergeList (msort firstPart) (msort secondPart)


type Function
    = Plus Function Function
    | Minus Function Function
    | Mult Function Function
    | Div Function Function
    | Poly Function Int
    | Const Int
    | X


print : Function -> String
print f =
    case f of
        X ->
            "x"

        Plus a b ->
            "(" ++ print a ++ " + " ++ print b ++ ")"

        Minus a b ->
            "(" ++ print a ++ " - " ++ print b ++ ")"

        Mult a b ->
            "(" ++ print a ++ " * " ++ print b ++ ")"

        Div a b ->
            "(" ++ print a ++ " / " ++ print b ++ ")"

        Poly a b ->
            "(" ++ print a ++ " ^ " ++ String.fromInt b ++ ")"

        Const a ->
            String.fromInt a


eval : Float -> Function -> Float
eval x f =
    case f of
        X ->
            x

        Plus a b ->
            eval x a + eval x b

        Minus a b ->
            eval x a - eval x b

        Mult a b ->
            eval x a * eval x b

        Div a b ->
            eval x a / eval x b

        Poly a b ->
            eval x a ^ toFloat b

        Const a ->
            toFloat a


graphLine : Function -> Int -> Int -> Int -> String
graphLine f x a b =
    let
        result =
            truncate <| eval (toFloat x) f
    in
    String.concat <|
        List.map
            (\y ->
                if y < result then
                    "*"

                else
                    "-"
            )
            (List.range a (b - 1))


graph : Function -> Int -> Int -> Int -> Int -> List String
graph f a b c d =
    List.map (\x -> graphLine f x c d) (List.range a (b - 1))



-- Week 5


above100 : Int -> Bool
above100 x =
    x > 100


repeatUntil : (a -> Bool) -> (a -> a) -> a -> a
repeatUntil fa fb x =
    let
        dNb =
            fb x
    in
    if fa x == False then
        repeatUntil fa fb dNb

    else
        x


myCollatz : List Int -> List Int
myCollatz xs =
    case xs of
        [] ->
            Debug.todo ""

        x :: _ ->
            if modBy 2 x == 0 then
                x // 2 :: xs

            else
                3 * x + 1 :: xs


derivative : Function -> Function
derivative f =
    case f of
        Plus a b ->
            Plus (derivative a) (derivative b)

        Minus a b ->
            Minus (derivative a) (derivative b)

        Poly a b ->
            Mult (Const b) (Poly a (b - 1))

        Mult a b ->
            Plus (Mult a (derivative b)) (Mult (derivative a) b)

        Div a b ->
            Div (Minus (Mult b (derivative a)) (Mult (derivative b) a)) (Poly b 2)

        Const _ ->
            Const 0

        X ->
            Const 1


simplify : Function -> Function
simplify f =
    case f of
        Plus a b ->
            let
                aa =
                    simplify a

                bb =
                    simplify b
            in
            case ( aa, bb ) of
                ( Const x, Const y ) ->
                    Const (x + y)

                ( _, Const 0 ) ->
                    aa

                ( Const 0, _ ) ->
                    bb

                _ ->
                    Plus aa bb

        Minus a b ->
            let
                aa =
                    simplify a

                bb =
                    simplify b
            in
            case ( aa, bb ) of
                ( Const x, Const y ) ->
                    Const (x - y)

                ( _, Const 0 ) ->
                    aa

                _ ->
                    Minus aa bb

        Mult a b ->
            let
                aa =
                    simplify a

                bb =
                    simplify b
            in
            case ( aa, bb ) of
                ( Const x, Const y ) ->
                    Const (x * y)

                ( _, Const 0 ) ->
                    Const 0

                ( Const 0, _ ) ->
                    Const 0

                ( _, Const 1 ) ->
                    aa

                ( Const 1, _ ) ->
                    bb

                _ ->
                    Plus aa bb

        Div a b ->
            let
                aa =
                    simplify a

                bb =
                    simplify b
            in
            case ( aa, bb ) of
                ( _, Const 1 ) ->
                    aa

                _ ->
                    Div aa bb

        Poly a b ->
            let
                aa =
                    simplify a
            in
            case ( aa, b ) of
                ( _, 0 ) ->
                    Const 1

                ( _, 1 ) ->
                    aa

                ( Const x, _ ) ->
                    Const (x ^ b)

                _ ->
                    Poly aa b

        _ ->
            f
