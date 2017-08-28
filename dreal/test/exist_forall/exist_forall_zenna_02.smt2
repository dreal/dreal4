;; https://github.com/dreal/dreal3/issues/139
;;
;; constraint1 = g(x) == f(x)
;;
(set-logic QF_NRA)
(declare-fun        t1 () Real [-10, 10])
(declare-fun        t2 () Real [-10, 10])
(declare-fun        t3 () Real [-10, 10])
(declare-fun        t4 () Real [-10, 10])
(declare-fun forall x  () Real [-10, 10])
(assert
 (forall ((x Real))
         (=
          (^ x 2)
          (+ t1
             (* t2 x)
             (* t3 (^ x 2))
             (* t4 (^ x 3))))))
(check-sat)
(exit)
