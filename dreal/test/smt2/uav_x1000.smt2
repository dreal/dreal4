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
(declare-fun x0_3 () Real)
(declare-fun x1_3 () Real)
(declare-fun x2_3 () Real)
(declare-fun x3_3 () Real)

(declare-fun bi_3 () Real)
(declare-fun b0_3 () Real)
(declare-fun b1_3 () Real)
(declare-fun b2_3 () Real)
(declare-fun b3_3 () Real)

(declare-fun qi_3 () Real)
(declare-fun q0_3 () Real)
(declare-fun q1_3 () Real)
(declare-fun q2_3 () Real)
(declare-fun q3_3 () Real)

(declare-fun t0_3 () Real)
(declare-fun t1_3 () Real)
(declare-fun t2_3 () Real)
(declare-fun t3_3 () Real)

;counterexample
(declare-fun bc_3 () Real)
(declare-fun qc_3 () Real)

(assert(>= t0_3 0))
(assert(>= t1_3 0))
(assert(>= t2_3 0))
(assert(>= t3_3 0))
(assert (<= bi_3 100))
(assert (<= b0_3 100))
(assert (<= b1_3 100))
(assert (<= b2_3 100))
(assert (<= b3_3 100))
(assert (>= qi_3 0))
(assert (>= q0_3 0))
(assert (>= q1_3 0))
(assert (>= q2_3 0))
(assert (>= q3_3 0))
(assert (<= x0_3 1000))
(assert (<= x1_3 1000))
(assert (<= x2_3 1000))
(assert (<= x3_3 1000))
(assert (>= x0_3 0))
(assert (>= x1_3 0))
(assert (>= x2_3 0))
(assert (>= x3_3 0))

;charging
(assert(= x0_3 0))
(assert(= b0_3 (+ bi_3 (* battery_charging_rate t0_3))))
(assert(= q0_3 (+ qi_3 (* queue_data_rate t0_3))))
;program: charge till battery >= 20
(assert (=> (>= bi_3 p2) (= b0_3 bi_3)))
(assert (or (=> (< bi_3 p2) (= b0_3 p2)) (= q0_3 100)))

;flying to D
(assert(= x1_3 1000))
(assert(= x1_3 (+ x0_3 (* drone_velocity t1_3))))
(assert(= b1_3 (- b0_3 (* battery_discharge_rate_fly t1_3))))
(assert(= q1_3 (+ q0_3 (* queue_data_rate t1_3))))

;emptying queue
(assert(= x2_3 1000))
(assert(= q2_3 (- q1_3 (* queue_upload_rate t2_3))))
(assert(= b2_3 (- b1_3 (* battery_discharge_rate_hover t2_3))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_3 p3) (= b2_3 p3)) (= q2_3 0)))
(assert (=> (<= b1_3 p3) (= b2_3 b1_3)))

;flying back
(assert(= x3_3 0))
(assert(= x3_3 (- x2_3 (* drone_velocity t3_3))))
(assert(= q3_3 (+ q2_3 (* queue_data_rate t3_3))))
(assert(= b3_3 (- b2_3 (* battery_discharge_rate_fly t3_3))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_3 100.0) (= qc_3 0.0))) here
(assert (and (= bc_3 100.0) (= qc_3 0.0)))

(assert (and (= bi_3 bc_3) (= qi_3 qc_3)))
(assert (=> (and (>= bi_3 p0) (<= qi_3 p1)) (and (> b0_3 0) (> b1_3 0) (> b2_3 0) (> b3_3 0) (< q0_3 100) (< q1_3 100) (< q2_3 100) (< q3_3 100) (and (>= b3_3 p0) (<= q3_3 p1)))))

(declare-fun x0_2 () Real)
(declare-fun x1_2 () Real)
(declare-fun x2_2 () Real)
(declare-fun x3_2 () Real)

(declare-fun bi_2 () Real)
(declare-fun b0_2 () Real)
(declare-fun b1_2 () Real)
(declare-fun b2_2 () Real)
(declare-fun b3_2 () Real)

(declare-fun qi_2 () Real)
(declare-fun q0_2 () Real)
(declare-fun q1_2 () Real)
(declare-fun q2_2 () Real)
(declare-fun q3_2 () Real)

(declare-fun t0_2 () Real)
(declare-fun t1_2 () Real)
(declare-fun t2_2 () Real)
(declare-fun t3_2 () Real)

;counterexample
(declare-fun bc_2 () Real)
(declare-fun qc_2 () Real)

(assert(>= t0_2 0))
(assert(>= t1_2 0))
(assert(>= t2_2 0))
(assert(>= t3_2 0))
(assert (<= bi_2 100))
(assert (<= b0_2 100))
(assert (<= b1_2 100))
(assert (<= b2_2 100))
(assert (<= b3_2 100))
(assert (>= qi_2 0))
(assert (>= q0_2 0))
(assert (>= q1_2 0))
(assert (>= q2_2 0))
(assert (>= q3_2 0))
(assert (<= x0_2 1000))
(assert (<= x1_2 1000))
(assert (<= x2_2 1000))
(assert (<= x3_2 1000))
(assert (>= x0_2 0))
(assert (>= x1_2 0))
(assert (>= x2_2 0))
(assert (>= x3_2 0))

;charging
(assert(= x0_2 0))
(assert(= b0_2 (+ bi_2 (* battery_charging_rate t0_2))))
(assert(= q0_2 (+ qi_2 (* queue_data_rate t0_2))))
;program: charge till battery >= 20
(assert (=> (>= bi_2 p2) (= b0_2 bi_2)))
(assert (or (=> (< bi_2 p2) (= b0_2 p2)) (= q0_2 100)))

;flying to D
(assert(= x1_2 1000))
(assert(= x1_2 (+ x0_2 (* drone_velocity t1_2))))
(assert(= b1_2 (- b0_2 (* battery_discharge_rate_fly t1_2))))
(assert(= q1_2 (+ q0_2 (* queue_data_rate t1_2))))

;emptying queue
(assert(= x2_2 1000))
(assert(= q2_2 (- q1_2 (* queue_upload_rate t2_2))))
(assert(= b2_2 (- b1_2 (* battery_discharge_rate_hover t2_2))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_2 p3) (= b2_2 p3)) (= q2_2 0)))
(assert (=> (<= b1_2 p3) (= b2_2 b1_2)))

;flying back
(assert(= x3_2 0))
(assert(= x3_2 (- x2_2 (* drone_velocity t3_2))))
(assert(= q3_2 (+ q2_2 (* queue_data_rate t3_2))))
(assert(= b3_2 (- b2_2 (* battery_discharge_rate_fly t3_2))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_2 50.01) (= qc_2 0.0))) here
(assert (and (= bc_2 50.01) (= qc_2 0.0)))

(assert (and (= bi_2 bc_2) (= qi_2 qc_2)))
(assert (=> (and (>= bi_2 p0) (<= qi_2 p1)) (and (> b0_2 0) (> b1_2 0) (> b2_2 0) (> b3_2 0) (< q0_2 100) (< q1_2 100) (< q2_2 100) (< q3_2 100) (and (>= b3_2 p0) (<= q3_2 p1)))))

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
(assert (<= x0_1 1000))
(assert (<= x1_1 1000))
(assert (<= x2_1 1000))
(assert (<= x3_1 1000))
(assert (>= x0_1 0))
(assert (>= x1_1 0))
(assert (>= x2_1 0))
(assert (>= x3_1 0))

;charging
(assert(= x0_1 0))
(assert(= b0_1 (+ bi_1 (* battery_charging_rate t0_1))))
(assert(= q0_1 (+ qi_1 (* queue_data_rate t0_1))))
;program: charge till battery >= 20
(assert (=> (>= bi_1 p2) (= b0_1 bi_1)))
(assert (or (=> (< bi_1 p2) (= b0_1 p2)) (= q0_1 100)))

;flying to D
(assert(= x1_1 1000))
(assert(= x1_1 (+ x0_1 (* drone_velocity t1_1))))
(assert(= b1_1 (- b0_1 (* battery_discharge_rate_fly t1_1))))
(assert(= q1_1 (+ q0_1 (* queue_data_rate t1_1))))

;emptying queue
(assert(= x2_1 1000))
(assert(= q2_1 (- q1_1 (* queue_upload_rate t2_1))))
(assert(= b2_1 (- b1_1 (* battery_discharge_rate_hover t2_1))))
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
; Add (assert (and (= bc_1 50.0) (= qc_1 0.0))) here
(assert (and (= bc_1 50.0) (= qc_1 0.0)))

(assert (and (= bi_1 bc_1) (= qi_1 qc_1)))
(assert (=> (and (>= bi_1 p0) (<= qi_1 p1)) (and (> b0_1 0) (> b1_1 0) (> b2_1 0) (> b3_1 0) (< q0_1 100) (< q1_1 100) (< q2_1 100) (< q3_1 100) (and (>= b3_1 p0) (<= q3_1 p1)))))



(check-sat)
(exit)
