; Declaring a point with X and Y coordinates
(declare-datatypes (T1 T2) ((Pair (mk-pair (col T1) (row T2)))))

; Declaring the coordinates of each triangle corner
(declare-const t1p1 (Pair Int Int))
(declare-const t1p2 (Pair Int Int))
(declare-const t1p3 (Pair Int Int))
(declare-const t2p1 (Pair Int Int))
(declare-const t2p2 (Pair Int Int))
(declare-const t2p3 (Pair Int Int))
(declare-const t3p1 (Pair Int Int))
(declare-const t3p2 (Pair Int Int))
(declare-const t3p3 (Pair Int Int))

; Each corner of the triangle has distinct coordinates
(assert (distinct t1p1 t1p2 t1p3 t3p1 t3p2 t3p3 t2p1 t2p2 t2p3))

; Setting ranges of the columns and row for each triangle corner
(assert
    (and
        (< 0 (col t1p1) 6)
        (< 0 (row t1p1) 6)
        (< 0 (col t1p2) 6)
        (< 0 (row t1p2) 6)
        (< 0 (col t1p3) 6)
        (< 0 (row t1p3) 6)
        (< 0 (col t2p1) 6)
        (< 0 (row t2p1) 6)
        (< 0 (col t2p2) 6)
        (< 0 (row t2p2) 6)
        (< 0 (col t2p3) 6)
        (< 0 (row t2p3) 6)
        (< 0 (col t3p1) 6)
        (< 0 (row t3p1) 6)
        (< 0 (col t3p2) 6)
        (< 0 (row t3p2) 6)
        (< 0 (col t3p3) 6)
        (< 0 (row t3p3) 6)
    )
)

; Checking that all corners of a triangle aren't on the same vertical or horizontal line
(assert
    (and
        (not (= (row t1p1) (row t1p2) (row t1p3)))
        (not (= (col t1p1) (col t1p2) (col t1p3)))
        (not (= (row t2p1) (row t2p2) (row t2p3)))
        (not (= (col t2p1) (col t2p2) (col t2p3)))
        (not (= (row t3p1) (row t3p2) (row t3p3)))
        (not (= (col t3p1) (col t3p2) (col t3p3)))
    )
)

; Telling our grid that if a corner is present on coordinates the cell is taken
;
; If the cell is taken, function returns true for those coordinates
; Otherwise, returns false
(define-fun cell ((i Int) (j Int)) Bool
    (xor
        (ite (and (= i (col t1p1)) (= j (row t1p1)))
            true
            (ite (and (= i (col t1p2)) (= j (row t1p2)))
                true
                (ite (and (= i (col t1p3)) (= j (row t1p3)))
                    true
                    (ite (and (= i (col t2p1)) (= j (row t2p1)))
                        true
                        (ite (and (= i (col t2p2)) (= j (row t2p2)))
                            true
                            (ite (and (= i (col t2p3)) (= j (row t2p3)))
                                true
                                (ite (and (= i (col t3p1)) (= j (row t3p1)))
                                    true
                                    (ite (and (= i (col t3p2)) (= j (row t3p2)))
                                        true
                                        (ite (and (= i (col t3p3)) (= j (row t3p3)))
                                            true
                                            false
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    )
)

; Function to set true to cells that are between corners
(assert
    (and
        ;t1p1 and t1p2 :
        ;row :
        (forall ((i Int) (j Int))
            (=> (and (= (row t1p1) (row t1p2) j) (or (< (col t1p1) i (col t1p2)) (< (col t1p2) i (col t1p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (row t1p1) (row t1p3) j) (or (< (col t1p1) i (col t1p3)) (< (col t1p3) i (col t1p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (row t1p2) (row t1p3) j) (or (< (col t1p2) i (col t1p3)) (< (col t1p3) i (col t1p2))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (row t2p1) (row t2p2) j) (or (< (col t2p1) i (col t2p2)) (< (col t2p2) i (col t2p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (row t2p1) (row t2p3) j) (or (< (col t2p1) i (col t2p3)) (< (col t2p3) i (col t2p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (row t2p2) (row t2p3) j) (or (< (col t2p2) i (col t2p3)) (< (col t2p3) i (col t2p2))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (row t3p1) (row t3p2) j) (or (< (col t3p1) i (col t3p2)) (< (col t3p2) i (col t3p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (row t3p1) (row t3p3) j) (or (< (col t3p1) i (col t3p3)) (< (col t3p3) i (col t3p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (row t3p2) (row t3p3) j) (or (< (col t3p2) i (col t3p3)) (< (col t3p3) i (col t3p2))))
                (= (cell i j) true)))

        ;col :
        (forall ((i Int) (j Int))
            (=> (and (= (col t1p1) (col t1p2) j) (or (< (row t1p1) i (row t1p2)) (< (row t1p2) i (row t1p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (col t1p1) (col t1p3) j) (or (< (row t1p1) i (row t1p3)) (< (row t1p3) i (row t1p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (col t1p2) (col t1p3) j) (or (< (row t1p2) i (row t1p3)) (< (row t1p3) i (row t1p2))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (col t2p1) (col t2p2) j) (or (< (row t2p1) i (row t2p2)) (< (row t2p2) i (row t2p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (col t2p1) (col t2p3) j) (or (< (row t2p1) i (row t2p3)) (< (row t2p3) i (row t2p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (col t2p2) (col t2p3) j) (or (< (row t2p2) i (row t2p3)) (< (row t2p3) i (row t2p2))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (col t3p1) (col t3p2) j) (or (< (row t3p1) i (row t3p2)) (< (row t3p2) i (row t3p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (col t3p1) (col t3p3) j) (or (< (row t3p1) i (row t3p3)) (< (row t3p3) i (row t3p1))))
                (= (cell i j) true)))
        (forall ((i Int) (j Int))
            (=> (and (= (col t3p2) (col t3p3) j) (or (< (col t3p2) i (col t3p3)) (< (col t3p3) i (col t3p2))))
                (= (cell i j) true)))

        (= (col t1p1) 1)
        (= (row t1p1) 1)
        (= (col t1p2) 5)
        (= (row t1p2) 1)
        (= (col t1p3) 1)
        (= (row t1p3) 5)
    )
)

;(assert (forall ((col Int) (row Int)) (= (cell col row) true)))
(check-sat)

;(get-model)
(echo "triangle 1")
(get-value ((col t1p1) (row t1p1) (col t1p2) (row t1p2) (col t1p3) (row t1p3)))
(echo "triangle 2")
(get-value ((col t2p1) (row t2p1) (col t2p2) (row t2p2) (col t2p3) (row t2p3)))
(echo "triangle 3")
(get-value ((col t3p1) (row t3p1) (col t3p2) (row t3p2) (col t3p3) (row t3p3)))
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