;; exp(-0.2) * sqrt(x1^2 + y1^2) + 3(cos(2 * x1) + sin(2 * y1))
;; Ackley4 Function
(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(declare-fun forall x2 () Real [-35.0, 35.0])
(declare-fun forall y2 () Real [-35.0, 35.0])
(declare-fun z () Real)
(assert (<= -35.0 x1))
(assert (<= x1 35.0))
(assert (<= -35.0 y1))
(assert (<= y1 35.0))
(assert
 (forall ((x2 Real) (y2 Real))
         (<=
          (+
           (+ (* (exp -0.2)
                 (sqrt (+ (^ x1 2)
                          (^ y1 2))))
              (* 3
                 (+ (cos (* 2 x1))
                    (sin (* 2 y1))))))
          (+
           (+ (* (exp -0.2)
                 (sqrt (+ (^ x2 2)
                          (^ y2 2))))
              (* 3
                 (+ (cos (* 2 x2))
                    (sin (* 2 y2)))))))))
(assert (= z
           (+
            (+ (* (exp -0.2)
                  (sqrt (+ (^ x1 2)
                           (^ y1 2))))
               (* 3
                  (+ (cos (* 2 x1))
                     (sin (* 2 y1))))))))
(check-sat)
(exit)
