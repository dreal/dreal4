(set-logic QF_NRA)
(declare-fun t () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun d1 () Real)
(declare-fun d2 () Real)
(declare-fun e1 () Real)
(declare-fun e2 () Real)
(assert (< 0 t))
(assert (< t 10))
(assert (< x1 -9))
(assert (< x2 -1))
(assert (> y1 10))
(assert (> y2 10))
(assert (< 0.1 d1))
(assert (< d1 0.15))
(assert (< 0.1 d2))
(assert (< d2 0.15))
(assert (< 0.1 e1))
(assert (< e1 0.15))
(assert (< 0.1 e2))
(assert (< e2 0.15))
(assert
	( < 
	   ( + 
		(^
		    (+
			( - ( - (- x1 y1) (* 100 d2) ) (* 100 e2) )
			(+ (* ( + (* 100 d2) (* 100 e2)) (cos (* 0.01 t)))
			(* (sin (* 0.01 t)) (- (* 100 d1) (* 100 e1))) )
		    )
		    2
		)
	
		(^
		    (+
			( + ( + (- x2 y2) (* 100 d1) ) (* 100 e1) )
			(+ (* ( + (* ( - 0 100) d1) (* (- 0 100) e1)) (cos (* 0.01 t)))
			(* (sin (* 0.01 t)) (- (* 100 d1) (* 100 e2))))
		    )
		    2
		)
	    )
	    2
	)
)
(check-sat)
(exit)
