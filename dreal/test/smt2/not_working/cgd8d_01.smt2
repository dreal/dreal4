(set-logic QF_NRA)
(set-option :precision 0.001)
(declare-fun x () Real [-1, 2])
(declare-fun forall y () Real [-1, 2])
(assert
    (forall ((y Real))
        (or
            (or
                (>= y 1)
                (<= y 0))
            (>= x y))))
(check-sat)
(exit)
