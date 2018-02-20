;; sin(x1) * exp((1 - cos(x2))^2) + cos(x2)exp((1 - sin(x1))^2) + (x1 - x2)^2
;; Bird Function
(set-logic QF_NRA)
(declare-fun x1 () Real [-6.283184, 6.283184])
(declare-fun x2 () Real [-6.283184, 6.283184])
(declare-fun z () Real)
(assert
 (forall ((y1 Real [-6.283184, 6.283184])
	  (y2 Real [-6.283184, 6.283184]))
         (<=
	  z
          (+
           (* (sin y1)
              (exp (^ (- 1 (cos y2)) 2)))
           (* (cos y2)
              (exp (^ (- 1 (sin y1)) 2)))
           (^ (- y1 y2) 2)))))
(assert (= z
           (+
            (* (sin x1)
               (exp (^ (- 1 (cos x2)) 2)))
            (* (cos x2)
               (exp (^ (- 1 (sin x1)) 2)))
            (^ (- x1 x2) 2))))
(check-sat)
(exit)
