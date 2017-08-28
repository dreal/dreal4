(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert
 (and
  (= x -3)
  (= y -4)
  (= z (arctan2 x y))
  (> z -2.4981)
  (> -2.4980 z)))
(check-sat)
(exit)
