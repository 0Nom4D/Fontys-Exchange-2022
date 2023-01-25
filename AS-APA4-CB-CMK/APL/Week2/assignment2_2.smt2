; Declaring Datatype for Pairs
(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

; Declaring possible pairs
; Variables are declared this way:
; => p.nb with nb the pair number of the round
; => r.nb with nb the test round number
(declare-const p1r1 (Pair Int Int))
(declare-const p2r1 (Pair Int Int))
(declare-const p3r1 (Pair Int Int))
(declare-const p1r2 (Pair Int Int))
(declare-const p2r2 (Pair Int Int))
(declare-const p3r2 (Pair Int Int))
(declare-const p1r3 (Pair Int Int))
(declare-const p2r3 (Pair Int Int))
(declare-const p3r3 (Pair Int Int))
(declare-const p1r4 (Pair Int Int))
(declare-const p2r4 (Pair Int Int))
(declare-const p3r4 (Pair Int Int))
(declare-const p1r5 (Pair Int Int))
(declare-const p2r5 (Pair Int Int))
(declare-const p3r5 (Pair Int Int))
(declare-const p1r6 (Pair Int Int))
(declare-const p2r6 (Pair Int Int))
(declare-const p3r6 (Pair Int Int))
(declare-const p1r7 (Pair Int Int))
(declare-const p2r7 (Pair Int Int))
(declare-const p3r7 (Pair Int Int))

; Reversed pairs
; Same thing as pairs above, except that we added a 'r' to symbolise the reversed pair
(declare-const rp1r1 (Pair Int Int))
(declare-const rp2r1 (Pair Int Int))
(declare-const rp3r1 (Pair Int Int))
(declare-const rp1r2 (Pair Int Int))
(declare-const rp2r2 (Pair Int Int))
(declare-const rp3r2 (Pair Int Int))
(declare-const rp1r3 (Pair Int Int))
(declare-const rp2r3 (Pair Int Int))
(declare-const rp3r3 (Pair Int Int))
(declare-const rp1r4 (Pair Int Int))
(declare-const rp2r4 (Pair Int Int))
(declare-const rp3r4 (Pair Int Int))
(declare-const rp1r5 (Pair Int Int))
(declare-const rp2r5 (Pair Int Int))
(declare-const rp3r5 (Pair Int Int))
(declare-const rp1r6 (Pair Int Int))
(declare-const rp2r6 (Pair Int Int))
(declare-const rp3r6 (Pair Int Int))
(declare-const rp1r7 (Pair Int Int))
(declare-const rp2r7 (Pair Int Int))
(declare-const rp3r7 (Pair Int Int))

; Checking that every pair of medecine in pairs is between 1 and 7
; Also checking that every pair per round create a triple of values x_, y_, z_
; Checking that values from every pair are distinct to be sure that x_, y_, z_ are all distincts
(assert (and (<= 1 (first p1r1) 7) (<= 1 (first p2r1) 7) (<= 1 (first p3r1) 7)))
(assert (and (<= 1 (second p1r1) 7) (<= 1 (second p2r1) 7) (<= 1 (second p3r1) 7)))
(assert (and (= (first p1r1) (first p2r1)) (= (second p2r1) (first p3r1)) (= (second p1r1) (second p3r1))))
(assert (and (distinct (first p1r1) (second p1r1)) (distinct (first p2r1) (second p2r1)) (distinct (first p3r1) (second p3r1))))

(assert (and (<= 1 (first p1r2) 7) (<= 1 (first p2r2) 7) (<= 1 (first p3r2) 7)))
(assert (and (<= 1 (second p1r2) 7) (<= 1 (second p2r2) 7) (<= 1 (second p3r2) 7)))
(assert (and (= (first p1r2) (first p2r2)) (= (second p2r2) (first p3r2)) (= (second p1r2) (second p3r2))))
(assert (and (distinct (first p1r2) (second p1r2)) (distinct (first p2r2) (second p2r2)) (distinct (first p3r2) (second p3r2))))

(assert (and (<= 1 (first p1r3) 7) (<= 1 (first p2r3) 7) (<= 1 (first p3r3) 7)))
(assert (and (<= 1 (second p1r3) 7) (<= 1 (second p2r3) 7) (<= 1 (second p3r3) 7)))
(assert (and (= (first p1r3) (first p2r3)) (= (second p2r3) (first p3r3)) (= (second p1r3) (second p3r3))))
(assert (and (distinct (first p1r3) (second p1r3)) (distinct (first p2r3) (second p2r3)) (distinct (first p3r3) (second p3r3))))

(assert (and (<= 1 (first p1r4) 7) (<= 1 (first p2r4) 7) (<= 1 (first p3r4) 7)))
(assert (and (<= 1 (second p1r4) 7) (<= 1 (second p2r4) 7) (<= 1 (second p3r4) 7)))
(assert (and (= (first p1r4) (first p2r4)) (= (second p2r4) (first p3r4)) (= (second p1r4) (second p3r4))))
(assert (and (distinct (first p1r4) (second p1r4)) (distinct (first p2r4) (second p2r4)) (distinct (first p3r4) (second p3r4))))

(assert (and (<= 1 (first p1r5) 7) (<= 1 (first p2r5) 7) (<= 1 (first p3r5) 7)))
(assert (and (<= 1 (second p1r5) 7) (<= 1 (second p2r5) 7) (<= 1 (second p3r5) 7)))
(assert (and (= (first p1r5) (first p2r5)) (= (second p2r5) (first p3r5)) (= (second p1r5) (second p3r5))))
(assert (and (distinct (first p1r5) (second p1r5)) (distinct (first p2r5) (second p2r5)) (distinct (first p3r5) (second p3r5))))

(assert (and (<= 1 (first p1r6) 7) (<= 1 (first p2r6) 7) (<= 1 (first p3r6) 7)))
(assert (and (<= 1 (second p1r6) 7) (<= 1 (second p2r6) 7) (<= 1 (second p3r6) 7)))
(assert (and (= (first p1r6) (first p2r6)) (= (second p2r6) (first p3r6)) (= (second p1r6) (second p3r6))))
(assert (and (distinct (first p1r6) (second p1r6)) (distinct (first p2r6) (second p2r6)) (distinct (first p3r6) (second p3r6))))

(assert (and (<= 1 (first p1r7) 7) (<= 1 (first p2r7) 7) (<= 1 (first p3r7) 7)))
(assert (and (<= 1 (second p1r7) 7) (<= 1 (second p2r7) 7) (<= 1 (second p3r7) 7)))
(assert (and (= (first p1r7) (first p2r7)) (= (second p2r7) (first p3r7)) (= (second p1r7) (second p3r7))))
(assert (and (distinct (first p1r7) (second p1r7)) (distinct (first p2r7) (second p2r7)) (distinct (first p3r7) (second p3r7))))

; Making every reversed pair from previously created pairs
(assert (and (= (first rp1r1) (second p1r1)) (= (second rp1r1) (first p1r1))))
(assert (and (= (first rp2r1) (second p2r1)) (= (second rp2r1) (first p2r1))))
(assert (and (= (first rp3r1) (second p3r1)) (= (second rp3r1) (first p3r1))))
(assert (and (= (first rp1r2) (second p1r2)) (= (second rp1r2) (first p1r2))))
(assert (and (= (first rp2r2) (second p2r2)) (= (second rp2r2) (first p2r2))))
(assert (and (= (first rp3r2) (second p3r2)) (= (second rp3r2) (first p3r2))))
(assert (and (= (first rp1r3) (second p1r3)) (= (second rp1r3) (first p1r3))))
(assert (and (= (first rp2r3) (second p2r3)) (= (second rp2r3) (first p2r3))))
(assert (and (= (first rp3r3) (second p3r3)) (= (second rp3r3) (first p3r3))))
(assert (and (= (first rp1r4) (second p1r4)) (= (second rp1r4) (first p1r4))))
(assert (and (= (first rp2r4) (second p2r4)) (= (second rp2r4) (first p2r4))))
(assert (and (= (first rp3r4) (second p3r4)) (= (second rp3r4) (first p3r4))))
(assert (and (= (first rp1r5) (second p1r5)) (= (second rp1r5) (first p1r5))))
(assert (and (= (first rp2r5) (second p2r5)) (= (second rp2r5) (first p2r5))))
(assert (and (= (first rp3r5) (second p3r5)) (= (second rp3r5) (first p3r5))))
(assert (and (= (first rp1r6) (second p1r6)) (= (second rp1r6) (first p1r6))))
(assert (and (= (first rp2r6) (second p2r6)) (= (second rp2r6) (first p2r6))))
(assert (and (= (first rp3r6) (second p3r6)) (= (second rp3r6) (first p3r6))))
(assert (and (= (first rp1r7) (second p1r7)) (= (second rp1r7) (first p1r7))))
(assert (and (= (first rp2r7) (second p2r7)) (= (second rp2r7) (first p2r7))))
(assert (and (= (first rp3r7) (second p3r7)) (= (second rp3r7) (first p3r7))))

; Being sure that every pair and reversed pair is distinct
(assert (distinct p1r1 p2r1 p3r1 p1r2 p2r2 p3r2 p1r3 p2r3 p3r3 p1r4 p2r4 p3r4 p1r5 p2r5 p3r5 p1r6 p2r6 p3r6 p1r7 p2r7 p3r7 rp1r1 rp2r1 rp3r1 rp1r2 rp2r2 rp3r2 rp1r3 rp2r3 rp3r3 rp1r4 rp2r4 rp3r4 rp1r5 rp2r5 rp3r5 rp1r6 rp2r6 rp3r6 rp1r7 rp2r7 rp3r7))

; Cheking if possible
(check-sat)
(get-value (p1r1 p2r1 p3r1 p1r2 p2r2 p3r2 p1r3 p2r3 p3r3 p1r4 p2r4 p3r4 p1r5 p2r5 p3r5 p1r6 p2r6 p3r6 p1r7 p2r7 p3r7))