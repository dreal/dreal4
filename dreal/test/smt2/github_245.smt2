(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(define-fun get_R ((x Real) (y Real)) Real
(* x (cos y)))
(assert (= a 12))
(assert (= b -0.7853981633974483))
(declare-fun R () Real)
;(assert (= R (* a (cos b))))
(assert (= R (get_R a b)))
(check-sat)
(get-model)

