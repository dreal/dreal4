(set-logic QF_NRA)
(set-option :forall-polytope true)
(declare-fun x () Real [4, 6])
;; sin(x)x² - cos(x)x
(minimize (- (* (sin x) (^ x 2))
             (* (cos x) x)))
(check-sat)
(exit)
