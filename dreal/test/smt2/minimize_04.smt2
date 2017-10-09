(set-logic QF_NRA)
(declare-fun x () Real [-1, 1])

;; x² <= 0.5 ∨ x² >= 0.8
(assert (or (<= (^ x 2) 0.5) (>= (^ x 2) 0.8)))

;; sin(x)
(minimize (sin x))

(check-sat)
(exit)
