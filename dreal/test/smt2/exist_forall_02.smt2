(set-logic QF_NRA)
(declare-fun x1 () Real [3.0, 3.14])
(assert
 (forall ((x2 Real [-7.0, 5.0]))
         (< (* x1 x2) 0)))
(check-sat)
(exit)
