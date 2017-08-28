;; cos(x1)sin(y1) - (x1 / (y1^2 +1))
;; Ackley4 Function
(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(declare-fun forall x2 () Real [-1.0, 2.0])
(declare-fun forall y2 () Real [-1.0, 1.0])
(declare-fun z () Real)
(assert (<= -1.0 x1))
(assert (<= x1 2.0))
(assert (<= -1.0 y1))
(assert (<= y1 1.0))
(assert
 (forall ((x2 Real) (y2 Real))
         (<=
          (- (* (cos x1)
                (sin y1))
             (/ x1
                (+ (^ y1 2)
                   1)))
          (- (* (cos x2)
                (sin y2))
             (/ x2
                (+ (^ y2 2)
                   1))))))
(assert (= z
           (- (* (cos x1)
                 (sin y1))
              (/ x1
                 (+ (^ y1 2)
                    1)))))
(check-sat)
(exit)
