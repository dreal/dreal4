(set-logic QF_NRA)
(declare-fun        a1 () Real [-10, 10])
(declare-fun forall x  () Real [-10, 10])

(assert
 (forall
  ((x Real)
   )
  (and
   (or (<= a1 x) (= (* -1.0 x) (abs x)))
   (or (>= a1 x) (= (*  1.0 x) (abs x)))
   )))

(check-sat)
(exit)
