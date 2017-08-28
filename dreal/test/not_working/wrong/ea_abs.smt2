;; exists a1, a2, a3
;; forall x, y
;; (assert (or (<= x a1) (> y (* a2 x)) (< (y (* a2 x))) (= y abs(x))))
;; (assert (or (<= x a1) (> y (* a3 x)) (< (y (* a3 x))) (= y abs(x))))

(set-logic QF_NRA)
(declare-fun        a1 () Real [-10, 10])
(declare-fun        a2 () Real [-10, 10])
(declare-fun        a3 () Real [-10, 10])
(declare-fun forall x  () Real [-10, 10])

(assert
 (forall
  ((x Real)
   )
  (and
   (or (<= a1 x) (= (* a2 x) (abs x)))
   (or (>  a1 x) (= (* a3 x) (abs x)))
   )))

(check-sat)
(exit)
