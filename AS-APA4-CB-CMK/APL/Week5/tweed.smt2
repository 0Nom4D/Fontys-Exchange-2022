(declare-datatypes () ((Days MON TUE WED THU FRI SAT SUN)))

(declare-fun lieDayDum (Int) Days)
(declare-fun lieDayDee (Int) Days)
(declare-const truthDayBoth Days)

(declare-const currentDay Days)

(declare-const aStatement Days)
(declare-const bStatement Days)

(declare-const A String)
(declare-const B String)

(assert (= aStatement SUN))
(assert (= bStatement TUE))

(assert
    (and
        (= (lieDayDum 0) MON)
        (= (lieDayDum 1) TUE)
        (= (lieDayDum 2) WED)

        (= (lieDayDee 0) THU)
        (= (lieDayDee 1) FRI)
        (= (lieDayDee 2) SAT)
    )
)

(assert (= truthDayBoth SUN))

(assert
    (and
        (or
            (= A "TWEEDLEDUM")
            (= A "TWEEDLEDEE")
        )
        (or
            (= B "TWEEDLEDUM")
            (= B "TWEEDLEDEE")
        )
        (distinct A B)
    )
)

(assert
    (implies (= currentDay truthDayBoth)
        (and
            (= currentDay aStatement)
            (= currentDay bStatement)
            (= A "TWEEDLEDUM")
            (= B "TWEEDLEDEE")
        )
    )
)

(check-sat)
(get-value (
    currentDay
    A
    B
))
