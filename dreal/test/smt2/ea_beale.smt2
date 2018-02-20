(set-logic QF_NRA)
(set-option :local-optimization true)
(set-option :polytope true)
(set-option :precision 0.01)
(declare-fun x1 () Real [-5.12, 5.12])
(declare-fun y1 () Real [-5.12, 5.12])
(assert
    (forall
        ((x2 Real [-5.12, 5.12]) (y2 Real [-5.12, 5.12]))
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
