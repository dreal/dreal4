(set-logic QF_NRA)
(define-fun b () Bool true)
(assert (or false b))
(check-sat)
