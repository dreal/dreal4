(set-logic QF_NRA)
(define-fun x () Real 5.0)
(assert (= x 5.0))  ; sat
(check-sat)
(get-model)
