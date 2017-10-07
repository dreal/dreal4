(set-logic QF_NRA)
(declare-fun x1 () Real [2, 50])
(declare-fun x2 () Real [-50, 50])

;; 10x₁ - x₂ ≥ 10
(assert (>= (- (* 10 x1) x2)
            10))

;; f = 0.01 x₁² + x₂² - 100
(minimize
 (-
  (+ (* 0.01 (^ x1 2))
     (^ x2 2))
  100))

;; Optimal at (2, 0.0)
(check-sat)
(exit)
