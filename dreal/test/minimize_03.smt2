(set-logic QF_NRA)
(declare-fun x1 () Real [-1, 1])
(declare-fun x2 () Real [-1, 1])

;; x₁² + x₂² <= 1
(assert (<= (+ (^ x1 2)
               (^ x2 2))
            1.0))

;; 100(x₂ - x₁)² + (1 - x₁)²
(minimize
 (+ (* 100
       (^ (- x2 x1) 2))
    (^ (- 1 x1) 2)))
(check-sat)
(exit)
