;; 200 * exp(-0.02 * sqrt(x1^2 + y1^2)) + 5 exp (cos(3 * x1) + sin(3 * y1))
;; Ackley3 Function
(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(declare-fun forall x2 () Real [-32.0, 32.0])
(declare-fun forall y2 () Real [-32.0, 32.0])
(declare-fun z () Real)
(assert (<= -32.0 x1))
(assert (<= x1 32.0))
(assert (<= -32.0 y1))
(assert (<= y1 32.0))
(assert
 (forall ((x2 Real) (y2 Real))
         (<=
          (+
           (* -200
              (exp (* -0.02
                      (sqrt (+ (^ x1 2)
                               (^ y1 2))))))
           (* 5
              (exp (+ (cos (* 3 x1))
                      (sin (* 3 y1))))))
          (+
           (* -200
              (exp (* -0.02
                      (sqrt (+ (^ x2 2)
                               (^ y2 2))))))
           (* 5
              (exp (+ (cos (* 3 x2))
                      (sin (* 3 y2)))))))))
(assert (= z
           (+
            (* -200
               (exp (* -0.02
                       (sqrt (+ (^ x1 2)
                                (^ y1 2))))))
            (* 5
               (exp (+ (cos (* 3 x1))
                       (sin (* 3 y1))))))))
(check-sat)
(exit)
