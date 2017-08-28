(set-logic QF_NRA)
(declare-fun x_0 () Real)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)

(assert (=  x_0  2))
(assert (=  x_1  x_0))
(assert (=  2  x_1))

(check-sat)
(exit)
