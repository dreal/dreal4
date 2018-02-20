(set-option :precision 0.1)
(set-logic QF_NRA)
(declare-fun base.dx_dt () Real)
(declare-fun base.q_a () Real)
(declare-fun base.q_a_dt () Real)
(declare-fun base.q_k () Real)
(declare-fun base.q_k_dt () Real)

;a solution
(assert (= base.dx_dt 40.0))
(assert (= base.q_a_dt 0.0))
(assert (= base.q_k_dt 0.0))

;constraints
(assert (= base.q_a 1.0))
(assert (= base.q_k 0.0))
(assert
    (=
        40.0
        (+
            (* 120.0 (^ base.q_k 3.0) base.q_k_dt)
            (* 120.0 (^ base.q_a 2.0) base.q_k base.q_k_dt)
            (* 120.0 base.q_a base.q_a_dt (^ base.q_k 2.0))
            (* (- 0.0 1.0) base.dx_dt (^ base.q_k 2.0))
            (* 120.0 (^ base.q_a 3.0) base.q_a_dt)
            (* base.dx_dt (^ base.q_a 2.0))
        )
    )
)

(check-sat)
(exit)
