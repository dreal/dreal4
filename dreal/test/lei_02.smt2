(set-logic QF_NRA)
(declare-fun x_0 () Real)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)

(assert (=  x_0  2))
(assert (=  x_1  x_0))
(assert (=  x_2  (tan 2)))
(assert (>  1  x_2))

(check-sat)
(exit)
