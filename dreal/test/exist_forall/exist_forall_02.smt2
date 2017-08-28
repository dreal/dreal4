(set-logic QF_NRA)
(declare-fun exists x1 () Real [3.0, 3.14])
(declare-fun forall x2 () Real [-7.0, 5.0])
(assert
 (forall ((x2 Real))
         (< (* x1 x2) 0)))
(check-sat)
(exit)
