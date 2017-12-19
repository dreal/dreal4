;; Author: Tristan Knoth
(set-logic QF_NRA)

;parameters
(declare-fun p0 () Real)
(declare-fun p1 () Real)
(declare-fun p2 () Real)
(declare-fun p3 () Real)

;constants
(declare-fun battery_charging_rate () Real)
(declare-fun battery_discharge_rate_fly () Real)
(declare-fun battery_discharge_rate_hover () Real)
(declare-fun queue_data_rate () Real)
(declare-fun queue_upload_rate () Real)
(declare-fun drone_velocity () Real)

(assert(= drone_velocity 10))
(assert(= battery_charging_rate 50))
(assert(= battery_discharge_rate_fly 1))
(assert(= battery_discharge_rate_hover 1))
(assert(= queue_data_rate 1))
(assert(= queue_upload_rate 1))

(assert (<= p0 100))
(assert (>= p0 0))
(assert (<= p1 100))
(assert (>= p1 0))
(assert (<= p2 100))
(assert (>= p2 0))
(assert (<= p3 100))
(assert (>= p3 0))

; Add all phi(counterexample) here
(declare-fun x0_1 () Real)
(declare-fun x1_1 () Real)
(declare-fun x2_1 () Real)
(declare-fun x3_1 () Real)

(declare-fun bi_1 () Real)
(declare-fun b0_1 () Real)
(declare-fun b1_1 () Real)
(declare-fun b2_1 () Real)
(declare-fun b3_1 () Real)

(declare-fun qi_1 () Real)
(declare-fun q0_1 () Real)
(declare-fun q1_1 () Real)
(declare-fun q2_1 () Real)
(declare-fun q3_1 () Real)

(declare-fun t0_1 () Real)
(declare-fun t1_1 () Real)
(declare-fun t2_1 () Real)
(declare-fun t3_1 () Real)

;counterexample
(declare-fun bc_1 () Real)
(declare-fun qc_1 () Real)

(assert(>= t0_1 0))
(assert(>= t1_1 0))
(assert(>= t2_1 0))
(assert(>= t3_1 0))
(assert (<= bi_1 100))
(assert (<= b0_1 100))
(assert (<= b1_1 100))
(assert (<= b2_1 100))
(assert (<= b3_1 100))
(assert (>= qi_1 0))
(assert (>= q0_1 0))
(assert (>= q1_1 0))
(assert (>= q2_1 0))
(assert (>= q3_1 0))
(assert (<= x0_1 10))
(assert (<= x1_1 10))
(assert (<= x2_1 10))
(assert (<= x3_1 10))
(assert (>= x0_1 0))
(assert (>= x1_1 0))
(assert (>= x2_1 0))
(assert (>= x3_1 0))

;charging
(assert (= x0_1 0))
(assert (= b0_1 (- (+ bi_1 (* battery_charging_rate t0_1) (* 1 (cos t0_1))))))
(assert (= q0_1 (- (+ qi_1 (* queue_data_rate t0_1)) (* 1 (cos t0_1)))))
;program: charge till battery >= 20
(assert (=> (>= bi_1 p2) (= b0_1 bi_1)))
(assert (or (=> (< bi_1 p2) (= b0_1 p2)) (= q0_1 100)))

;flying to D
(assert (= x1_1 10))
(assert (= x1_1 (- (+ x0_1 (* drone_velocity t1_1)) (* 5 (cos t1_1)))))
(assert (= b1_1 (+ (- b0_1 (* battery_discharge_rate_fly t1_1)) (* 5 (cos t1_1)))))
(assert (= q1_1 (- (+ q0_1 (* queue_data_rate t1_1)) (* 5 (cos t1_1)))))


;emptying queue
(assert (= x2_1 10))
(assert (= q2_1 (- (- q1_1 (* queue_upload_rate t2_1)) (* 5 (cos t2_1)))))
(assert (= b2_1 (- (- b1_1 (* battery_discharge_rate_hover t2_1)) (* 5 (cos t2_1)))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_1 p3) (= b2_1 p3)) (= q2_1 0)))
(assert (=> (<= b1_1 p3) (= b2_1 b1_1)))

;flying back
(assert(= x3_1 0))
(assert(= x3_1 (- x2_1 (* drone_velocity t3_1))))
(assert(= q3_1 (+ q2_1 (* queue_data_rate t3_1))))
(assert(= b3_1 (- b2_1 (* battery_discharge_rate_fly t3_1))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_1 9.085103094369515) (= qc_1 0.0))) here
(assert (and (= bc_1 9.085103094369515) (= qc_1 0.0)))

(assert (and (= bi_1 bc_1) (= qi_1 qc_1)))
(assert (=> (and (>= bi_1 p0) (<= qi_1 p1)) (and (> b0_1 0) (> b1_1 0) (> b2_1 0) (> b3_1 0) (< q0_1 100) (< q1_1 100) (< q2_1 100) (< q3_1 100) (and (>= b3_1 p0) (<= q3_1 p1)))))



(check-sat)
(exit)
