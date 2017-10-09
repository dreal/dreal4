(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun forall x2 () Real [0.0, 7.0])
(declare-fun x3 () Real)
(assert (<= 0.0 x1))
(assert (<= x1 7.0))
(assert
 (forall ((x2 Real))
         (<=
          (- (* (sin x1) (^ x1 2))
             (* (cos x1) x1))
          (- (* (sin x2) (^ x2 2))
             (* (cos x2) x2)))))
(assert (= x3
           (- (* (sin x1) (^ x1 2))
              (* (cos x1) x1))))
(check-sat)
(exit)
