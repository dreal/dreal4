;; exp(-0.2) * sqrt(x1^2 + y1^2) + 3(cos(2 * x1) + sin(2 * y1))
;; Ackley4 Function
(set-logic QF_NRA)
(declare-fun x1 () Real [-35, 35])
(declare-fun y1 () Real [-35, 35])
(declare-fun z () Real)
(assert
 (forall ((x2 Real [-35.0, 35.0]) (y2 Real [-35.0, 35.0]))
         (<=
	  z
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
