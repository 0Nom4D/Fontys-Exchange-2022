; Declaring Datatype for Pairs
(declare-datatypes (X Y) ((Corner (mk-corner (row Y) (col X)))))

(declare-const triangle1Corner1 (Corner Int Int))
(declare-const triangle1Corner2 (Corner Int Int))
(declare-const triangle1Corner3 (Corner Int Int))

(declare-const triangle2Corner1 (Corner Int Int))
(declare-const triangle2Corner2 (Corner Int Int))
(declare-const triangle2Corner3 (Corner Int Int))

(declare-const triangle3Corner1 (Corner Int Int))
(declare-const triangle3Corner2 (Corner Int Int))
(declare-const triangle3Corner3 (Corner Int Int))

(declare-const gridSize Int)

(declare-fun grid (Int Int) Bool)

(assert (= gridSize 5))

(define-fun isOnVerticalLine ((colCorner1 Int) (colCorner2 Int)) Bool
    (= colCorner1 colCorner2)
)

(define-fun isOnHorizontalLine ((rowCorner1 Int) (rowCorner2 Int)) Bool
    (= rowCorner1 rowCorner2)
)

(define-fun isOnRightSidedDiagonalLine ((colCorner1 Int) (rowCorner1 Int) (colCorner2 Int) (rowCorner2 Int)) Bool
    (or
        (and
            (= colCorner2 (+ colCorner1 1))
            (or
                (= rowCorner1 (+ rowCorner2 1))
                (= rowCorner1 (- rowCorner2 1))
            )
        )
        (and
            (= colCorner2 (+ colCorner1 2))
            (or
                (= rowCorner1 (+ rowCorner2 2))
                (= rowCorner1 (- rowCorner2 2))
            )
        )
        (and
            (= colCorner2 (+ colCorner1 3))
            (or
                (= rowCorner1 (+ rowCorner2 3))
                (= rowCorner1 (- rowCorner2 3))
            )
        )
        (and
            (= colCorner2 (+ colCorner1 4))
            (or
                (= rowCorner1 (+ rowCorner2 4))
                (= rowCorner1 (- rowCorner2 4))
            )
        )
        (and
            (= colCorner2 (+ colCorner1 5))
            (or
                (= rowCorner1 (+ rowCorner2 5))
                (= rowCorner1 (- rowCorner2 5))
            )
        )
    )
)

(define-fun isOnLeftSidedDiagonalLine ((colCorner1 Int) (rowCorner1 Int) (colCorner2 Int) (rowCorner2 Int)) Bool
    (or
        (and
            (= colCorner2 (- colCorner1 1))
            (or
                (= rowCorner1 (+ rowCorner2 1))
                (= rowCorner1 (- rowCorner2 1))
            )
        )
        (and
            (= colCorner2 (- colCorner1 2))
            (or
                (= rowCorner1 (+ rowCorner2 2))
                (= rowCorner1 (- rowCorner2 2))
            )
        )
        (and
            (= colCorner2 (- colCorner1 3))
            (or
                (= rowCorner1 (+ rowCorner2 3))
                (= rowCorner1 (- rowCorner2 3))
            )
        )
        (and
            (= colCorner2 (- colCorner1 4))
            (or
                (= rowCorner1 (+ rowCorner2 4))
                (= rowCorner1 (- rowCorner2 4))
            )
        )
        (and
            (= colCorner2 (- colCorner1 5))
            (or
                (= rowCorner1 (+ rowCorner2 5))
                (= rowCorner1 (- rowCorner2 5))
            )
        )
    )
)

(assert
    (forall ((col Int) (row Int))
        
    )
)

(check-sat)
; (echo "Row 1")
; (get-value ((grid 1 1) (grid 1 2) (grid 1 3) (grid 1 4) (grid 1 5)))
; (echo "Row 2")
; (get-value ((grid 2 1) (grid 2 2) (grid 2 3) (grid 2 4) (grid 2 5)))
; (echo "Row 3")
; (get-value ((grid 3 1) (grid 3 2) (grid 3 3) (grid 3 4) (grid 3 5)))
; (echo "Row 4")
; (get-value ((grid 4 1) (grid 4 2) (grid 4 3) (grid 4 4) (grid 4 5)))
; (echo "Row 5")
; (get-value ((grid 5 1) (grid 5 2) (grid 5 3) (grid 5 4) (grid 5 5)))
