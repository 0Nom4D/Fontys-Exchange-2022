; Defining Enum for City Type
(declare-datatypes () ((City CIT1 CIT2 CIT3 CIT4 CIT5 CIT6)))

; Function to get the different cities the salesman went to
(declare-fun seenCities (Int) City)

; Function to get the different possible paths values between cities
;
; With 2 cities as parameters, we will have the cost of the path between those 2 cities
(declare-fun paths (City City) Int)

; Function to get the different connections between the cities
;
; If 2 cities are connected by a path, the result of the function will be true
; Otherwise, it will be false
(declare-fun connections (City City) Bool)

; Defines the starting city
(declare-const startPath City)

; Function to get the cost of the path when the salesman traveled to x cities
(declare-fun pathCost (Int) Int)

; Value to define the maximum number of cities the salesman can go to
(declare-const maxNumberCity Int)

; Clauses to define the initial state of the program
(assert (= (seenCities 1) CIT1))
(assert (= (pathCost 1) 0))
(assert (= maxNumberCity 6))

; Assertion to tell there is no path between all cities except the ones defined in the (not (and ...)) clauses
;
; The values that are excluded in the (not (and ...)) clauses will be set to true and have a path between them.
(assert
    (forall ((city1 City) (city2 City))
        (implies (and
            (not (and (= city1 CIT1) (= city2 CIT2)))
            (not (and (= city1 CIT2) (= city2 CIT1)))

            (not (and (= city1 CIT1) (= city2 CIT3)))
            (not (and (= city1 CIT3) (= city2 CIT1)))

            (not (and (= city1 CIT2) (= city2 CIT3)))
            (not (and (= city1 CIT3) (= city2 CIT2)))

            (not (and (= city1 CIT2) (= city2 CIT4)))
            (not (and (= city1 CIT4) (= city2 CIT2)))

            (not (and (= city1 CIT2) (= city2 CIT5)))
            (not (and (= city1 CIT5) (= city2 CIT2)))

            (not (and (= city1 CIT3) (= city2 CIT5)))
            (not (and (= city1 CIT5) (= city2 CIT3)))

            (not (and (= city1 CIT3) (= city2 CIT6)))
            (not (and (= city1 CIT6) (= city2 CIT3)))

            (not (and (= city1 CIT4) (= city2 CIT5)))
            (not (and (= city1 CIT5) (= city2 CIT4)))

            (not (and (= city1 CIT5) (= city2 CIT6)))
            (not (and (= city1 CIT6) (= city2 CIT5)))
        )
        (= (connections city1 city2) false)
    ))
)

; Setting up the cost of the paths between the cities
(assert
    (and
        (= (paths CIT1 CIT2) 6)
        (= (paths CIT2 CIT1) 6)
        (= (connections CIT1 CIT2) true)
        (= (connections CIT2 CIT1) true)

        (= (paths CIT1 CIT3) 7)
        (= (paths CIT3 CIT1) 7)
        (= (connections CIT1 CIT3) true)
        (= (connections CIT3 CIT1) true)

        (= (paths CIT2 CIT3) 1)
        (= (paths CIT3 CIT2) 1)
        (= (connections CIT2 CIT3) true)
        (= (connections CIT3 CIT2) true)

        (= (paths CIT2 CIT4) 4)
        (= (paths CIT4 CIT2) 4)
        (= (connections CIT2 CIT4) true)
        (= (connections CIT4 CIT2) true)

        (= (paths CIT2 CIT5) 3)
        (= (paths CIT5 CIT2) 3)
        (= (connections CIT2 CIT5) true)
        (= (connections CIT5 CIT2) true)

        (= (paths CIT3 CIT5) 2)
        (= (paths CIT5 CIT3) 2)
        (= (connections CIT3 CIT5) true)
        (= (connections CIT5 CIT3) true)

        (= (paths CIT3 CIT6) 1)
        (= (paths CIT6 CIT3) 1)
        (= (connections CIT3 CIT6) true)
        (= (connections CIT6 CIT3) true)

        (= (paths CIT4 CIT5) 5)
        (= (paths CIT5 CIT4) 5)
        (= (connections CIT4 CIT5) true)
        (= (connections CIT5 CIT4) true)

        (= (paths CIT5 CIT6) 3)
        (= (paths CIT6 CIT5) 3)
        (= (connections CIT5 CIT6) true)
        (= (connections CIT6 CIT5) true)
    )
)

; Assertion to make the basic behaviour
;
; Each time the salesman travels to a new city, the city he travels to is added to the function seenCities
; if a connection between those 2 is true.
; The cost of the path is also added to the cost of the path between the 2 cities we chose to go.
(assert
    (forall ((pathStep Int))
        (implies (and (<= 1 pathStep maxNumberCity))
            (and
                (= (connections (seenCities pathStep) (seenCities (+ pathStep 1))) true)
                (= (pathCost (+ pathStep 1)) (+ (pathCost pathStep) (paths (seenCities pathStep) (seenCities (+ pathStep 1)))))
            )
        )
    )
)

; Using Minimize Optimization on the cost of the final pathCost
(minimize (pathCost maxNumberCity))

; The salesman should travel to each city only once
(assert
    (distinct
        (seenCities 1)
        (seenCities 2)
        (seenCities 3)
        (seenCities 4)
        (seenCities 5)
        (seenCities 6)
    )
)

(check-sat)
(get-value (
    (pathCost maxNumberCity)
    (seenCities 1)
    (seenCities 2)
    (seenCities 3)
    (seenCities 4)
    (seenCities 5)
    (seenCities 6)
))
