;; cos(x1)sin(y1) - (x1 / (y1^2 +1))
;; Ackley4 Function
(set-logic QF_NRA)
(declare-fun x1 () Real [-1, 2])
(declare-fun y1 () Real [-1, 2])
(declare-fun z () Real)
(assert
 (forall ((x2 Real [-1.0, 2.0]) (y2 Real [-1.0, 1.0]))
         (<=
	  z
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
