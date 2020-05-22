(declare-const w Real)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (xor (>= w 10) (>= x -10) (>= y 10) (>= z -10)))
(assert (= w 0))   ; false
(assert (= x 0))   ; true
(assert (= y 20))  ; true
(assert (= z 0))   ; true
(check-sat)
(exit)
