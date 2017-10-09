(set-logic QF_NRA)
(declare-fun exists x1 () Real [-5.12, 5.12])
(declare-fun exists y1 () Real [-5.12, 5.12])
(declare-fun forall x2 () Real [-5.12, 5.12])
(declare-fun forall y2 () Real [-5.12, 5.12])
(assert
    (forall
        ((x2 Real) (y2 Real))
        (<=
            ;; (1.5 - x + x * y) ^ 2 +
            ;; (2.25 - x + x * y^2) ^2 +
            ;; (2.625 - x + x*y^3)^2
            (+
                (^ (+
                       (- 1.5
                           x1)
                       (* x1 y1))
                    2)
                (^
                    (+
                        (- 2.25
                            x1)
                        (* x1 (^ y1 2)))
                    2)
                (^
                    (+
                        (- 2.625
                            x1)
                        (* x1 (^ y1 3)))
                    2))
            (+
                (^ (+
                       (- 1.5
                           x2)
                       (* x2 y2))
                    2)
                (^
                    (+
                        (- 2.25
                            x2)
                        (* x2 (^ y2 2)))
                    2)

                (^
                    (+
                        (- 2.625
                            x2)
                        (* x2 (^ y2 3)))
                    2)))))
(check-sat)
(exit)
