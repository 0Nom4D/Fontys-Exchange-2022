; column and row parameters for number of visible skyscrapers
(declare-fun coltop (Int) Int)
(declare-fun colbot (Int) Int)
(declare-fun rowleft (Int) Int)
(declare-fun rowright (Int) Int)

; Adding the constraints to rows and columns
(assert
    (and
        (= (coltop 1) 3) (= (colbot 1) 2)
        (= (coltop 2) 1) (= (colbot 2) 5)
        (= (coltop 3) 3) (= (colbot 3) 3)
        (= (coltop 4) 2) (= (colbot 4) 2)
        (= (coltop 5) 2) (= (colbot 5) 1)
        (= (rowleft 1) 2) (= (rowright 1) 2)
        (= (rowleft 2) 3) (= (rowright 2) 2)
        (= (rowleft 3) 2) (= (rowright 3) 3)
        (= (rowleft 4) 1) (= (rowright 4) 3)
        (= (rowleft 5) 3) (= (rowright 5) 1)
    )
)

; Function used to keep our grid states
(declare-fun cell (Int Int) Int) ; format = cell column=i row=j

; Checks that every cell of the grid has a value between 1 and 5
(assert
    (forall ((i Int) (j Int))
        (<= 1 (cell i j) 5)
    )
)

; Checking that every value in rows and in columns are distinct
(assert
    (and
        (forall ((i Int))
            (distinct (cell i 1) (cell i 2) (cell i 3) (cell i 4) (cell i 5))
        )
        (forall ((j Int))
            (distinct (cell 1 j) (cell 2 j) (cell 3 j) (cell 4 j) (cell 5 j))
        )
    )
)


(assert
    (and
        ; 1/5 row
        ; Those clauses checks that the constraints 1 and 5 are respected by the solver when solving the rows.
        (forall ((j Int))
            (=> (= (rowleft j) 1)
                (= (cell 1 j) 5)
            )
        )
        (forall ((j Int))
            (=> (= (rowleft j) 5)
                (and (= (cell 1 j) 1) (= (cell 2 j) 2) (= (cell 3 j) 3) (= (cell 4 j) 4) (= (cell 5 j) 5))
            )
        )
        (forall ((j Int))
            (=> (= (rowright j) 1)
                (= (cell 5 j) 5)
            )
        )
        (forall ((j Int))
            (=> (= (rowright j) 5)
                (and (= (cell 5 j) 1) (= (cell 4 j) 2) (= (cell 3 j) 3) (= (cell 2 j) 4) (= (cell 1 j) 5))
            )
        )

        ;1/5 col
        ; Those clauses checks that the constraints 1 and 5 are respected by the solver when solving the columns.
        (forall ((i Int))
            (=> (= (coltop i) 1)
                (= (cell i 1) 5)
            )
        )
        (forall ((i Int))
            (=> (= (coltop i) 5)
                (and (= (cell i 1) 1) (= (cell i 2) 2) (= (cell i 3) 3) (= (cell i 4) 4) (= (cell i 5) 5))
            )
        )
        (forall ((i Int))
            (=> (= (colbot i) 1)
                (= (cell i 5) 5)
            )
        )
        (forall ((i Int))
            (=> (= (colbot i) 5)
                (and (= (cell i 5) 1) (= (cell i 4) 2) (= (cell i 3) 3) (= (cell i 2) 4) (= (cell i 1) 5))
            )
        )

        ;2 row
        ; Those clauses checks that the constraint 2 is respected by the solver when solving the rows.
        (forall ((j Int)) (=> (= (rowleft j) 2)
            (or
                (and (< (cell 1 j) (cell 2 j)) (> (cell 2 j) (cell 3 j)) (> (cell 2 j) (cell 4 j)) (> (cell 2 j) (cell 5 j)))
                (and (< (cell 1 j) (cell 3 j)) (> (cell 1 j) (cell 2 j)) (> (cell 3 j) (cell 4 j)) (> (cell 3 j) (cell 5 j)))
                (and (< (cell 1 j) (cell 4 j)) (> (cell 1 j) (cell 2 j)) (> (cell 1 j) (cell 3 j)) (> (cell 4 j) (cell 5 j)))
                (and (< (cell 1 j) (cell 5 j)) (> (cell 1 j) (cell 2 j)) (> (cell 1 j) (cell 3 j)) (> (cell 1 j) (cell 4 j)))
            ))
        )
        (forall ((j Int)) (=> (= (rowright j) 2)
            (or
                (and (< (cell 5 j) (cell 4 j)) (> (cell 4 j) (cell 3 j)) (> (cell 4 j) (cell 2 j)) (> (cell 4 j) (cell 1 j)))
                (and (< (cell 5 j) (cell 3 j)) (> (cell 5 j) (cell 4 j)) (> (cell 3 j) (cell 2 j)) (> (cell 3 j) (cell 1 j)))
                (and (< (cell 5 j) (cell 2 j)) (> (cell 5 j) (cell 4 j)) (> (cell 5 j) (cell 3 j)) (> (cell 2 j) (cell 1 j)))
                (and (< (cell 5 j) (cell 1 j)) (> (cell 5 j) (cell 4 j)) (> (cell 5 j) (cell 3 j)) (> (cell 5 j) (cell 2 j)))
            ))
        )

        ;2 col
        ; Those clauses checks that the constraint 2 is respected by the solver when solving the columns.
        (forall ((i Int)) (=> (= (coltop i) 2)
            (or
                (and (< (cell i 1) (cell i 2)) (> (cell i 2) (cell i 3)) (> (cell i 2) (cell i 4)) (> (cell i 2) (cell i 5)))
                (and (< (cell i 1) (cell i 3)) (> (cell i 1) (cell i 2)) (> (cell i 3) (cell i 4)) (> (cell i 3) (cell i 5)))
                (and (< (cell i 1) (cell i 4)) (> (cell i 1) (cell i 2)) (> (cell i 1) (cell i 3)) (> (cell i 4) (cell i 5)))
                (and (< (cell i 1) (cell i 5)) (> (cell i 1) (cell i 2)) (> (cell i 1) (cell i 3)) (> (cell i 1) (cell i 4)))
            ))
        )
        (forall ((i Int)) (=> (= (colbot i) 2)
            (or
                (and (< (cell i 5) (cell i 4)) (> (cell i 4) (cell i 3)) (> (cell i 4) (cell i 2)) (> (cell i 4) (cell i 1)))
                (and (< (cell i 5) (cell i 3)) (> (cell i 5) (cell i 4)) (> (cell i 3) (cell i 2)) (> (cell i 3) (cell i 1)))
                (and (< (cell i 5) (cell i 2)) (> (cell i 5) (cell i 4)) (> (cell i 5) (cell i 3)) (> (cell i 2) (cell i 1)))
                (and (< (cell i 5) (cell i 1)) (> (cell i 5) (cell i 4)) (> (cell i 5) (cell i 3)) (> (cell i 5) (cell i 2)))
            ))
        )

        ;3 row
        ; Those clauses checks that the constraint 3 is respected by the solver when solving the rows.
        (forall ((j Int)) (=> (= (rowleft j) 3)
            (or
                (and (< (cell 1 j) (cell 2 j)) (< (cell 2 j) (cell 3 j)) (> (cell 3 j) (cell 4 j)) (> (cell 3 j) (cell 5 j)))
                (and (< (cell 1 j) (cell 2 j)) (< (cell 2 j) (cell 4 j)) (> (cell 2 j) (cell 3 j)) (> (cell 4 j) (cell 5 j)))
                (and (< (cell 1 j) (cell 2 j)) (< (cell 2 j) (cell 5 j)) (> (cell 2 j) (cell 3 j)) (> (cell 2 j) (cell 4 j)))
                (and (< (cell 1 j) (cell 3 j)) (< (cell 3 j) (cell 4 j)) (> (cell 1 j) (cell 2 j)) (> (cell 4 j) (cell 5 j)))
                (and (< (cell 1 j) (cell 3 j)) (< (cell 3 j) (cell 5 j)) (> (cell 1 j) (cell 2 j)) (> (cell 3 j) (cell 4 j)))
                (and (< (cell 1 j) (cell 4 j)) (< (cell 4 j) (cell 5 j)) (> (cell 1 j) (cell 2 j)) (> (cell 1 j) (cell 3 j)))
            ))
        )
        (forall ((j Int)) (=> (= (rowright j) 3)
            (or
                (and (< (cell 5 j) (cell 4 j)) (< (cell 4 j) (cell 3 j)) (> (cell 3 j) (cell 2 j)) (> (cell 3 j) (cell 1 j)))
                (and (< (cell 5 j) (cell 4 j)) (< (cell 4 j) (cell 2 j)) (> (cell 4 j) (cell 3 j)) (> (cell 2 j) (cell 1 j)))
                (and (< (cell 5 j) (cell 4 j)) (< (cell 4 j) (cell 1 j)) (> (cell 4 j) (cell 3 j)) (> (cell 4 j) (cell 2 j)))
                (and (< (cell 5 j) (cell 3 j)) (< (cell 3 j) (cell 2 j)) (> (cell 5 j) (cell 4 j)) (> (cell 2 j) (cell 1 j)))
                (and (< (cell 5 j) (cell 3 j)) (< (cell 3 j) (cell 1 j)) (> (cell 5 j) (cell 4 j)) (> (cell 3 j) (cell 2 j)))
                (and (< (cell 5 j) (cell 2 j)) (< (cell 2 j) (cell 1 j)) (> (cell 5 j) (cell 4 j)) (> (cell 5 j) (cell 3 j)))
            ))
        )

        ;3 col
        ; Those clauses checks that the constraint 3 is respected by the solver when solving the columns.
        (forall ((i Int)) (=> (= (coltop i) 3)
            (or
                (and (< (cell i 1) (cell i 2)) (< (cell i 2) (cell i 3)) (> (cell i 3) (cell i 4)) (> (cell i 3) (cell i 5)))
                (and (< (cell i 1) (cell i 2)) (< (cell i 2) (cell i 4)) (> (cell i 2) (cell i 3)) (> (cell i 4) (cell i 5)))
                (and (< (cell i 1) (cell i 2)) (< (cell i 2) (cell i 5)) (> (cell i 2) (cell i 3)) (> (cell i 2) (cell i 4)))
                (and (< (cell i 1) (cell i 3)) (< (cell i 3) (cell i 4)) (> (cell i 1) (cell i 2)) (> (cell i 4) (cell i 5)))
                (and (< (cell i 1) (cell i 3)) (< (cell i 3) (cell i 5)) (> (cell i 1) (cell i 2)) (> (cell i 3) (cell i 4)))
                (and (< (cell i 1) (cell i 4)) (< (cell i 4) (cell i 5)) (> (cell i 1) (cell i 2)) (> (cell i 1) (cell i 3)))
            ))
        )
        (forall ((i Int)) (=> (= (colbot i) 3)
            (or
                (and (< (cell i 5) (cell i 4)) (< (cell i 4) (cell i 3)) (> (cell i 3) (cell i 2)) (> (cell i 3) (cell i 1)))
                (and (< (cell i 5) (cell i 4)) (< (cell i 4) (cell i 2)) (> (cell i 4) (cell i 3)) (> (cell i 2) (cell i 1)))
                (and (< (cell i 5) (cell i 4)) (< (cell i 4) (cell i 1)) (> (cell i 4) (cell i 3)) (> (cell i 4) (cell i 2)))
                (and (< (cell i 5) (cell i 3)) (< (cell i 3) (cell i 2)) (> (cell i 5) (cell i 4)) (> (cell i 2) (cell i 1)))
                (and (< (cell i 5) (cell i 3)) (< (cell i 3) (cell i 1)) (> (cell i 5) (cell i 4)) (> (cell i 3) (cell i 2)))
                (and (< (cell i 5) (cell i 2)) (< (cell i 2) (cell i 1)) (> (cell i 5) (cell i 4)) (> (cell i 5) (cell i 3)))
            ))
        )

        ;4 row
        ; Those clauses checks that the constraint 4 is respected by the solver when solving the rows.
        (forall ((j Int)) (=> (= (rowleft j) 4)
            (or
                (and (< (cell 1 j) (cell 2 j) (cell 3 j) (cell 4 j)) (> (cell 4 j) (cell 5 j)))
                (and (< (cell 1 j) (cell 2 j) (cell 3 j) (cell 5 j)) (> (cell 3 j) (cell 4 j)))
                (and (< (cell 1 j) (cell 2 j) (cell 4 j) (cell 5 j)) (> (cell 2 j) (cell 3 j)))
                (and (< (cell 1 j) (cell 3 j) (cell 4 j) (cell 5 j)) (> (cell 1 j) (cell 2 j)))
            ))
        )
        (forall ((j Int)) (=> (= (rowright j) 4)
            (or
                (and (< (cell 5 j) (cell 4 j) (cell 3 j) (cell 2 j)) (> (cell 2 j) (cell 1 j)))
                (and (< (cell 5 j) (cell 4 j) (cell 3 j) (cell 1 j)) (> (cell 3 j) (cell 2 j)))
                (and (< (cell 5 j) (cell 4 j) (cell 2 j) (cell 1 j)) (> (cell 4 j) (cell 3 j)))
                (and (< (cell 5 j) (cell 3 j) (cell 2 j) (cell 1 j)) (> (cell 5 j) (cell 4 j)))
            ))
        )

        ;4 col
        ; Those clauses checks that the constraint 4 is respected by the solver when solving the columns.
        (forall ((i Int)) (=> (= (coltop i) 4)
            (or
                (and (< (cell i 1) (cell i 2) (cell i 3) (cell i 4)) (> (cell i 4) (cell i 5)))
                (and (< (cell i 1) (cell i 2) (cell i 3) (cell i 5)) (> (cell i 3) (cell i 4)))
                (and (< (cell i 1) (cell i 2) (cell i 4) (cell i 5)) (> (cell i 2) (cell i 3)))
                (and (< (cell i 1) (cell i 3) (cell i 4) (cell i 5)) (> (cell i 1) (cell i 2)))
            ))
        )
        (forall ((i Int)) (=> (= (colbot i) 4)
            (or
                (and (< (cell i 5) (cell i 4) (cell i 3) (cell i 2)) (> (cell i 2) (cell i 1)))
                (and (< (cell i 5) (cell i 4) (cell i 3) (cell i 1)) (> (cell i 3) (cell i 2)))
                (and (< (cell i 5) (cell i 4) (cell i 2) (cell i 1)) (> (cell i 4) (cell i 3)))
                (and (< (cell i 5) (cell i 3) (cell i 2) (cell i 1)) (> (cell i 5) (cell i 4)))
            ))
        )
    )
)

; Checking if the problem is solvable
(check-sat)

; Displaying awnser if the problem is solvable, otherwise throws an error
(echo "row1")
(get-value ((cell 1 1) (cell 2 1) (cell 3 1) (cell 4 1) (cell 5 1)))
(echo "row2")
(get-value ((cell 1 2) (cell 2 2) (cell 3 2) (cell 4 2) (cell 5 2)))
(echo "row3")
(get-value ((cell 1 3) (cell 2 3) (cell 3 3) (cell 4 3) (cell 5 3)))
(echo "row4")
(get-value ((cell 1 4) (cell 2 4) (cell 3 4) (cell 4 4) (cell 5 4)))
(echo "row5")
(get-value ((cell 1 5) (cell 2 5) (cell 3 5) (cell 4 5) (cell 5 5)))