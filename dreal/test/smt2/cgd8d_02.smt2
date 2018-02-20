;; https://github.com/dreal/dreal3/issues/337
(set-logic QF_NRA)
(set-option :precision 0.00001)
(declare-fun x () Real [-1, 2])
(assert (forall ((w Real [-3.141593, 3.141593]))
		(or (< (cos w) 0.3) (<= 0.4 x))))
(check-sat)
(exit)
