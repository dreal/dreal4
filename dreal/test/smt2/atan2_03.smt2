(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert
 (and
  (= x 3)
  (= y -4)
  (= z (arctan2 x y))
  (< 2.4980 z)
  (< z 2.4981)))
(check-sat)
(exit)
