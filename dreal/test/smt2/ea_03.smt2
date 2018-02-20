(set-logic QF_NRA)
(declare-fun x1 () Real [-3.0, 3.14])
(assert
 (forall
  ((x2 Real [7.0, 50.0]))
  (and
   (>= x2 20)
   (<= x1 x2))))
(check-sat)
(exit)
