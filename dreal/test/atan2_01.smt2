(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert
 (and
  (= x 3)
  (= y 4)
  (= z (arctan2 x y))
  (< 0.64350 z)
  (< z 0.64351)))
(check-sat)
(exit)
