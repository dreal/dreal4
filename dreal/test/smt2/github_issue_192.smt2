;; From https://github.com/dreal/dreal4/issues/192
(set-logic QF_NRA)
(set-option :worklist-fixpoint true)
(declare-fun _substvar_157_ () Bool)
(declare-const r0 Real)
(declare-const r2 Real)
(assert (and (< r2 26760.9911) _substvar_157_))
(assert (< (- 8.787792382 567495437.0 r0 65964.0 2865083.0) 2865083.0))
(check-sat)
