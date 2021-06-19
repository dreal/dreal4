(declare-fun x () Int)
(declare-fun y () Int)

(assert
 (and
  (= x 100)
  (> x y)
  (or (>= x 0)
      (>= y 0))))

(check-sat)
