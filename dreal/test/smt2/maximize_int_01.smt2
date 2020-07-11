;; https://github.com/dreal/dreal4/issues/210
(set-logic QF_NRA)
(declare-const i Int)
(assert (< i 100))
(assert (< 1 i))
(maximize i)
(check-sat)
(get-model)
(exit)
