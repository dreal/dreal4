(set-logic QF_NRA)
(assert (= 0 (let ((a (+ 6 5))) (- a 11))))
(check-sat)
(exit)
