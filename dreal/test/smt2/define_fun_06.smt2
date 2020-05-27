(set-logic QF_NRA)
(define-fun b () Bool false)
(assert (or false b))
(check-sat)
