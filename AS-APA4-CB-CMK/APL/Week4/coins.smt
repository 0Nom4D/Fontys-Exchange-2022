(declare-const denomination_1 Int)
(declare-const denomination_2 Int)
(declare-const denomination_3 Int)

(declare-const d1_nb_p1 Int)
(declare-const d2_nb_p1 Int)
(declare-const d3_nb_p1 Int)

(declare-const d1_nb_p2 Int)
(declare-const d2_nb_p2 Int)
(declare-const d3_nb_p2 Int)

(declare-const d1_nb_p3 Int)
(declare-const d2_nb_p3 Int)
(declare-const d3_nb_p3 Int)

; The value of each denomination should be higher than 0
; Each denomination should also be unique because, otherwise that's the same denomination as others
(assert (distinct denomination_1 denomination_2 denomination_3))
(assert
    (and
        (> denomination_1 0)
        (> denomination_2 0)
        (> denomination_3 0)
    )
)

; The number of denomination by amount should be 0 or more
; The total of all number of denomination should be 3
(assert
    (and
        (>= d1_nb_p1 0)
        (>= d2_nb_p1 0)
        (>= d3_nb_p1 0)
        (= (+ d1_nb_p1 d2_nb_p1 d3_nb_p1) 3)
    )
)

(assert
    (and
        (>= d1_nb_p2 0)
        (>= d2_nb_p2 0)
        (>= d3_nb_p2 0)
        (= (+ d1_nb_p2 d2_nb_p2 d3_nb_p2) 3)
    )
)

(assert
    (and
        (>= d1_nb_p3 0)
        (>= d2_nb_p3 0)
        (>= d3_nb_p3 0)
        (= (+ d1_nb_p3 d2_nb_p3 d3_nb_p3) 3)
    )
)

; The amount for each round should be respected
(assert (= (+ (* denomination_1 d1_nb_p1) (* denomination_2 d2_nb_p1) (* denomination_3 d3_nb_p1)) 20))
(assert (= (+ (* denomination_1 d1_nb_p2) (* denomination_2 d2_nb_p2) (* denomination_3 d3_nb_p2)) 23))
(assert (= (+ (* denomination_1 d1_nb_p3) (* denomination_2 d2_nb_p3) (* denomination_3 d3_nb_p3)) 29))

(check-sat-using smt)
(get-value
    (
        denomination_1
        denomination_2
        denomination_3

        d1_nb_p1
        d2_nb_p1
        d3_nb_p1

        d1_nb_p2
        d2_nb_p2
        d3_nb_p2

        d1_nb_p3
        d2_nb_p3
        d3_nb_p3
    )
)
