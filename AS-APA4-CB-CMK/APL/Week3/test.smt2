(declare-fun m() Int)
(declare-fun s() Int)
(declare-fun h() Int)
(declare-fun t() Int)
(declare-fun l() Int)
(declare-fun v() Int)

(assert
    (and
        (<= 1 m 6)
        (<= 1 s 6)
        (<= 1 h 6)
        (<= 1 t 6)
        (<= 1 l 6)
        (<= 1 v 6)

        (distinct m s h t v l)

        ; condition 1
        (>= s 2) ; or we change line 15 to (< 1 s 7)

        ; condition 2
        (=> (< h l) (< m l))

        ; condition 3
        (and (< s m) (< s v))

        ; consition 4
        (or (< t h) (< t v))
        (not(and(< t h) (< t v)))
    )
)

(assert (< h s t m l v))

(check-sat-using smt)
(get-model)