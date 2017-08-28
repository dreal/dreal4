(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (< 2.4 x))
(assert (< x 2.6))
(assert (< -10.0 y))
(assert (< y 10.0))
(assert 
	(and
		(= y (cos x))
	)
)
(check-sat)
(exit)
