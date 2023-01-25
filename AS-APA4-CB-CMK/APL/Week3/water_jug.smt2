(set-option :produce-models true)

; Function to check a water jug at step X
(declare-fun jugAtStep (Int Int) Int)

; Number of the final step
(declare-const end_step Int)

; Function to get the max capacity of a water jug
(declare-fun max (Int) Int)

; Function to get the total amount of water at step X
(define-fun getTotalWater ((step Int)) Int
    (+ (jugAtStep step 1) (jugAtStep step 2) (jugAtStep step 3))
)

; We're setting the maximum capacities
(assert
    (and
        (= (max 1) 8)
        (= (max 2) 5)
        (= (max 3) 3)
    )
)

; We're setting our initial state
(assert
    (and
        (= (jugAtStep 0 1) 8)
        (= (jugAtStep 0 2) 0)
        (= (jugAtStep 0 3) 0)
    )
)

; We're setting our final state
(assert
    (and
        (= (jugAtStep end_step 1) 4)
        (= (jugAtStep end_step 2) 4)
        (= (jugAtStep end_step 3) 0)
    )
)

; Restricting values for water jugs
;
; We're checking that at every step the total water is equal to the total water at the step further.
; We're also restricting our water jugs values between 0 and their maximum capacity.
(assert
    (forall ((step Int))
        (implies (<= 0 step end_step)
            (and
                (<= 0 (jugAtStep step 1) (max 1))
                (<= 0 (jugAtStep step 2) (max 2))
                (<= 0 (jugAtStep step 3) (max 3))
                (= (getTotalWater step) (getTotalWater (+ step 1)))
            )
        )
    )
)

; Loop to pour water from a jug to another
;
; Since the amount of water doesn't change from a step to another
; we must have the same amount of water all along.
; Moreover, when we pour water from a jug to another, one water jug
; water amount doesn't change. Only the two others changes (sender and receiver).
; This function is made to pour water from a jug to another and to stop whenever
; a water jug is at 0 or if the other is at max capacity.
(assert
    (forall ((step Int))
        (implies (<= 0 step end_step)
            (exists ((jug1 Int) (jug2 Int) (jug3 Int))
                (and
                    (distinct jug1 jug2 jug3)
                    (<= 1 jug1 3)
                    (<= 1 jug2 3)
                    (<= 1 jug3 3)

                    (= (jugAtStep step jug1) (jugAtStep (+ step 1) jug1))
                    (distinct (jugAtStep step jug2) (jugAtStep (+ step 1) jug2))
                    (distinct (jugAtStep step jug3) (jugAtStep (+ step 1) jug3))

                    (or
                        (= (jugAtStep (+ step 1) jug2) 0)
                        (= (jugAtStep (+ step 1) jug3) (max jug3))
                    )
                )
            )
        )
    )
)

; Checking that our number of step doesn't exceeds 10
(assert (<= 0 end_step 10))

; Checking the satisfiability of the problem
(check-sat-using smt)

; Getting the model values for the answer
(get-value (
    end_step
    (jugAtStep 0 1)
    (jugAtStep 0 2)
    (jugAtStep 0 3)

    (jugAtStep 1 1)
    (jugAtStep 1 2)
    (jugAtStep 1 3)

    (jugAtStep 2 1)
    (jugAtStep 2 2)
    (jugAtStep 2 3)

    (jugAtStep 3 1)
    (jugAtStep 3 2)
    (jugAtStep 3 3)

    (jugAtStep 4 1)
    (jugAtStep 4 2)
    (jugAtStep 4 3)

    (jugAtStep 5 1)
    (jugAtStep 5 2)
    (jugAtStep 5 3)

    (jugAtStep 6 1)
    (jugAtStep 6 2)
    (jugAtStep 6 3)

    (jugAtStep 7 1)
    (jugAtStep 7 2)
    (jugAtStep 7 3)

    (jugAtStep 8 1)
    (jugAtStep 8 2)
    (jugAtStep 8 3)

    (jugAtStep 9 1)
    (jugAtStep 9 2)
    (jugAtStep 9 3)

    (jugAtStep 10 1)
    (jugAtStep 10 2)
    (jugAtStep 10 3)

    )
)
