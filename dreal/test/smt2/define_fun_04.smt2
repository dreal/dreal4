(set-logic QF_NRA)
(define-fun x () Real 5.0)
(assert (= x 0.0))  ; unsat
(check-sat)
