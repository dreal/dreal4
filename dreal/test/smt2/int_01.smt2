(set-logic QF_NRA)
(declare-fun a () Int [-10, 10])
(declare-fun b () Int [-10, 10])
(declare-fun c () Int [-10, 10])
(assert (= 1
           (+
            (* (^ a b) c)
            (* 10 a)
            b)))
(assert (< a 10))
(assert (< b 10))
(assert (= c 5))
(check-sat)
(exit)
