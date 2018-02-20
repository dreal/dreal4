(set-logic QF_NRA)

(assert (= 0xAB.CDp+12 703696.0))

(assert (= 0x0.A 0.625))     ;; exponent omitted
(assert (= 0xBp+2 44))       ;; point omitted
(assert (= 0xA. 10))         ;; fractional part omitted
(assert (= 0x.A 0.625))      ;; integer part omitted
(assert (= +0x0.Ap+0 0.625)) ;; plus sign prefix

(check-sat)
(exit)
