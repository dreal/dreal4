(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (<= -1 x))
(assert (<=  x 5))

(assert (<= -1 y))
(assert (<=  y 5))

(assert (<= -2.6 z))
(assert (<=  z -2.55))

(assert 
	( or 
		(and
			(and (<= 0 x) (<= x 0.4))
			(and (<= 0 y) (<= y 0.4))
		)
		(and
			(and (<= 0 x) (<= y 0.4))
			(and (<= 0 y) (<= y 0.4))
		)
	)
)
(assert 
	( >
		(-
			(* 0.4878 (+ (^ x 2) (^ y 2)))
			(+ 0.66 ( * 1.3701 (+ x y)))
		)
		z
	)
)
(check-sat)
(exit)
