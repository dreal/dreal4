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
(declare-fun x0_10 () Real)
(declare-fun x1_10 () Real)
(declare-fun x2_10 () Real)
(declare-fun x3_10 () Real)

(declare-fun bi_10 () Real)
(declare-fun b0_10 () Real)
(declare-fun b1_10 () Real)
(declare-fun b2_10 () Real)
(declare-fun b3_10 () Real)

(declare-fun qi_10 () Real)
(declare-fun q0_10 () Real)
(declare-fun q1_10 () Real)
(declare-fun q2_10 () Real)
(declare-fun q3_10 () Real)

(declare-fun t0_10 () Real)
(declare-fun t1_10 () Real)
(declare-fun t2_10 () Real)
(declare-fun t3_10 () Real)

;counterexample
(declare-fun bc_10 () Real)
(declare-fun qc_10 () Real)

(assert(>= t0_10 0))
(assert(>= t1_10 0))
(assert(>= t2_10 0))
(assert(>= t3_10 0))
(assert (<= bi_10 100))
(assert (<= b0_10 100))
(assert (<= b1_10 100))
(assert (<= b2_10 100))
(assert (<= b3_10 100))
(assert (>= qi_10 0))
(assert (>= q0_10 0))
(assert (>= q1_10 0))
(assert (>= q2_10 0))
(assert (>= q3_10 0))
(assert (<= x0_10 10))
(assert (<= x1_10 10))
(assert (<= x2_10 10))
(assert (<= x3_10 10))
(assert (>= x0_10 0))
(assert (>= x1_10 0))
(assert (>= x2_10 0))
(assert (>= x3_10 0))

;charging
(assert(= x0_10 0))
(assert(= b0_10 (+ bi_10 (* battery_charging_rate t0_10))))
(assert(= q0_10 (+ qi_10 (* queue_data_rate t0_10))))
;program: charge till battery >= 20
(assert (=> (>= bi_10 p2) (= b0_10 bi_10)))
(assert (or (=> (< bi_10 p2) (= b0_10 p2)) (= q0_10 100)))

;flying to D
(assert(= x1_10 10))
(assert(= x1_10 (+ x0_10 (* drone_velocity t1_10))))
(assert(= b1_10 (- b0_10 (* battery_discharge_rate_fly t1_10))))
(assert(= q1_10 (+ q0_10 (* queue_data_rate t1_10))))

;emptying queue
(assert(= x2_10 10))
(assert(= q2_10 (- q1_10 (* queue_upload_rate t2_10))))
(assert(= b2_10 (- b1_10 (* battery_discharge_rate_hover t2_10))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_10 p3) (= b2_10 p3)) (= q2_10 0)))
(assert (=> (<= b1_10 p3) (= b2_10 b1_10)))

;flying back
(assert(= x3_10 0))
(assert(= x3_10 (- x2_10 (* drone_velocity t3_10))))
(assert(= q3_10 (+ q2_10 (* queue_data_rate t3_10))))
(assert(= b3_10 (- b2_10 (* battery_discharge_rate_fly t3_10))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_10 3.01368122874133) (= qc_10 1.366307996766999e-2))) here
(assert (and (= bc_10 3.01368122874133) (= qc_10 1.366307996766999e-2)))

(assert (and (= bi_10 bc_10) (= qi_10 qc_10)))
(assert (=> (and (>= bi_10 p0) (<= qi_10 p1)) (and (> b0_10 0) (> b1_10 0) (> b2_10 0) (> b3_10 0) (< q0_10 100) (< q1_10 100) (< q2_10 100) (< q3_10 100) (and (>= b3_10 p0) (<= q3_10 p1)))))

(declare-fun x0_9 () Real)
(declare-fun x1_9 () Real)
(declare-fun x2_9 () Real)
(declare-fun x3_9 () Real)

(declare-fun bi_9 () Real)
(declare-fun b0_9 () Real)
(declare-fun b1_9 () Real)
(declare-fun b2_9 () Real)
(declare-fun b3_9 () Real)

(declare-fun qi_9 () Real)
(declare-fun q0_9 () Real)
(declare-fun q1_9 () Real)
(declare-fun q2_9 () Real)
(declare-fun q3_9 () Real)

(declare-fun t0_9 () Real)
(declare-fun t1_9 () Real)
(declare-fun t2_9 () Real)
(declare-fun t3_9 () Real)

;counterexample
(declare-fun bc_9 () Real)
(declare-fun qc_9 () Real)

(assert(>= t0_9 0))
(assert(>= t1_9 0))
(assert(>= t2_9 0))
(assert(>= t3_9 0))
(assert (<= bi_9 100))
(assert (<= b0_9 100))
(assert (<= b1_9 100))
(assert (<= b2_9 100))
(assert (<= b3_9 100))
(assert (>= qi_9 0))
(assert (>= q0_9 0))
(assert (>= q1_9 0))
(assert (>= q2_9 0))
(assert (>= q3_9 0))
(assert (<= x0_9 10))
(assert (<= x1_9 10))
(assert (<= x2_9 10))
(assert (<= x3_9 10))
(assert (>= x0_9 0))
(assert (>= x1_9 0))
(assert (>= x2_9 0))
(assert (>= x3_9 0))

;charging
(assert(= x0_9 0))
(assert(= b0_9 (+ bi_9 (* battery_charging_rate t0_9))))
(assert(= q0_9 (+ qi_9 (* queue_data_rate t0_9))))
;program: charge till battery >= 20
(assert (=> (>= bi_9 p2) (= b0_9 bi_9)))
(assert (or (=> (< bi_9 p2) (= b0_9 p2)) (= q0_9 100)))

;flying to D
(assert(= x1_9 10))
(assert(= x1_9 (+ x0_9 (* drone_velocity t1_9))))
(assert(= b1_9 (- b0_9 (* battery_discharge_rate_fly t1_9))))
(assert(= q1_9 (+ q0_9 (* queue_data_rate t1_9))))

;emptying queue
(assert(= x2_9 10))
(assert(= q2_9 (- q1_9 (* queue_upload_rate t2_9))))
(assert(= b2_9 (- b1_9 (* battery_discharge_rate_hover t2_9))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_9 p3) (= b2_9 p3)) (= q2_9 0)))
(assert (=> (<= b1_9 p3) (= b2_9 b1_9)))

;flying back
(assert(= x3_9 0))
(assert(= x3_9 (- x2_9 (* drone_velocity t3_9))))
(assert(= q3_9 (+ q2_9 (* queue_data_rate t3_9))))
(assert(= b3_9 (- b2_9 (* battery_discharge_rate_fly t3_9))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_9 3.00686896929951) (= qc_9 6.384710306227026e-3))) here
(assert (and (= bc_9 3.00686896929951) (= qc_9 6.384710306227026e-3)))

(assert (and (= bi_9 bc_9) (= qi_9 qc_9)))
(assert (=> (and (>= bi_9 p0) (<= qi_9 p1)) (and (> b0_9 0) (> b1_9 0) (> b2_9 0) (> b3_9 0) (< q0_9 100) (< q1_9 100) (< q2_9 100) (< q3_9 100) (and (>= b3_9 p0) (<= q3_9 p1)))))

(declare-fun x0_8 () Real)
(declare-fun x1_8 () Real)
(declare-fun x2_8 () Real)
(declare-fun x3_8 () Real)

(declare-fun bi_8 () Real)
(declare-fun b0_8 () Real)
(declare-fun b1_8 () Real)
(declare-fun b2_8 () Real)
(declare-fun b3_8 () Real)

(declare-fun qi_8 () Real)
(declare-fun q0_8 () Real)
(declare-fun q1_8 () Real)
(declare-fun q2_8 () Real)
(declare-fun q3_8 () Real)

(declare-fun t0_8 () Real)
(declare-fun t1_8 () Real)
(declare-fun t2_8 () Real)
(declare-fun t3_8 () Real)

;counterexample
(declare-fun bc_8 () Real)
(declare-fun qc_8 () Real)

(assert(>= t0_8 0))
(assert(>= t1_8 0))
(assert(>= t2_8 0))
(assert(>= t3_8 0))
(assert (<= bi_8 100))
(assert (<= b0_8 100))
(assert (<= b1_8 100))
(assert (<= b2_8 100))
(assert (<= b3_8 100))
(assert (>= qi_8 0))
(assert (>= q0_8 0))
(assert (>= q1_8 0))
(assert (>= q2_8 0))
(assert (>= q3_8 0))
(assert (<= x0_8 10))
(assert (<= x1_8 10))
(assert (<= x2_8 10))
(assert (<= x3_8 10))
(assert (>= x0_8 0))
(assert (>= x1_8 0))
(assert (>= x2_8 0))
(assert (>= x3_8 0))

;charging
(assert(= x0_8 0))
(assert(= b0_8 (+ bi_8 (* battery_charging_rate t0_8))))
(assert(= q0_8 (+ qi_8 (* queue_data_rate t0_8))))
;program: charge till battery >= 20
(assert (=> (>= bi_8 p2) (= b0_8 bi_8)))
(assert (or (=> (< bi_8 p2) (= b0_8 p2)) (= q0_8 100)))

;flying to D
(assert(= x1_8 10))
(assert(= x1_8 (+ x0_8 (* drone_velocity t1_8))))
(assert(= b1_8 (- b0_8 (* battery_discharge_rate_fly t1_8))))
(assert(= q1_8 (+ q0_8 (* queue_data_rate t1_8))))

;emptying queue
(assert(= x2_8 10))
(assert(= q2_8 (- q1_8 (* queue_upload_rate t2_8))))
(assert(= b2_8 (- b1_8 (* battery_discharge_rate_hover t2_8))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_8 p3) (= b2_8 p3)) (= q2_8 0)))
(assert (=> (<= b1_8 p3) (= b2_8 b1_8)))

;flying back
(assert(= x3_8 0))
(assert(= x3_8 (- x2_8 (* drone_velocity t3_8))))
(assert(= q3_8 (+ q2_8 (* queue_data_rate t3_8))))
(assert(= b3_8 (- b2_8 (* battery_discharge_rate_fly t3_8))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_8 2.075147753699873e-3) (= qc_8 7.830028072417344))) here
(assert (and (= bc_8 2.075147753699873e-3) (= qc_8 7.830028072417344)))

(assert (and (= bi_8 bc_8) (= qi_8 qc_8)))
(assert (=> (and (>= bi_8 p0) (<= qi_8 p1)) (and (> b0_8 0) (> b1_8 0) (> b2_8 0) (> b3_8 0) (< q0_8 100) (< q1_8 100) (< q2_8 100) (< q3_8 100) (and (>= b3_8 p0) (<= q3_8 p1)))))

(declare-fun x0_7 () Real)
(declare-fun x1_7 () Real)
(declare-fun x2_7 () Real)
(declare-fun x3_7 () Real)

(declare-fun bi_7 () Real)
(declare-fun b0_7 () Real)
(declare-fun b1_7 () Real)
(declare-fun b2_7 () Real)
(declare-fun b3_7 () Real)

(declare-fun qi_7 () Real)
(declare-fun q0_7 () Real)
(declare-fun q1_7 () Real)
(declare-fun q2_7 () Real)
(declare-fun q3_7 () Real)

(declare-fun t0_7 () Real)
(declare-fun t1_7 () Real)
(declare-fun t2_7 () Real)
(declare-fun t3_7 () Real)

;counterexample
(declare-fun bc_7 () Real)
(declare-fun qc_7 () Real)

(assert(>= t0_7 0))
(assert(>= t1_7 0))
(assert(>= t2_7 0))
(assert(>= t3_7 0))
(assert (<= bi_7 100))
(assert (<= b0_7 100))
(assert (<= b1_7 100))
(assert (<= b2_7 100))
(assert (<= b3_7 100))
(assert (>= qi_7 0))
(assert (>= q0_7 0))
(assert (>= q1_7 0))
(assert (>= q2_7 0))
(assert (>= q3_7 0))
(assert (<= x0_7 10))
(assert (<= x1_7 10))
(assert (<= x2_7 10))
(assert (<= x3_7 10))
(assert (>= x0_7 0))
(assert (>= x1_7 0))
(assert (>= x2_7 0))
(assert (>= x3_7 0))

;charging
(assert(= x0_7 0))
(assert(= b0_7 (+ bi_7 (* battery_charging_rate t0_7))))
(assert(= q0_7 (+ qi_7 (* queue_data_rate t0_7))))
;program: charge till battery >= 20
(assert (=> (>= bi_7 p2) (= b0_7 bi_7)))
(assert (or (=> (< bi_7 p2) (= b0_7 p2)) (= q0_7 100)))

;flying to D
(assert(= x1_7 10))
(assert(= x1_7 (+ x0_7 (* drone_velocity t1_7))))
(assert(= b1_7 (- b0_7 (* battery_discharge_rate_fly t1_7))))
(assert(= q1_7 (+ q0_7 (* queue_data_rate t1_7))))

;emptying queue
(assert(= x2_7 10))
(assert(= q2_7 (- q1_7 (* queue_upload_rate t2_7))))
(assert(= b2_7 (- b1_7 (* battery_discharge_rate_hover t2_7))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_7 p3) (= b2_7 p3)) (= q2_7 0)))
(assert (=> (<= b1_7 p3) (= b2_7 b1_7)))

;flying back
(assert(= x3_7 0))
(assert(= x3_7 (- x2_7 (* drone_velocity t3_7))))
(assert(= q3_7 (+ q2_7 (* queue_data_rate t3_7))))
(assert(= b3_7 (- b2_7 (* battery_discharge_rate_fly t3_7))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_7 3.0) (= qc_7 0.0))) here
(assert (and (= bc_7 3.0) (= qc_7 0.0)))

(assert (and (= bi_7 bc_7) (= qi_7 qc_7)))
(assert (=> (and (>= bi_7 p0) (<= qi_7 p1)) (and (> b0_7 0) (> b1_7 0) (> b2_7 0) (> b3_7 0) (< q0_7 100) (< q1_7 100) (< q2_7 100) (< q3_7 100) (and (>= b3_7 p0) (<= q3_7 p1)))))

(declare-fun x0_6 () Real)
(declare-fun x1_6 () Real)
(declare-fun x2_6 () Real)
(declare-fun x3_6 () Real)

(declare-fun bi_6 () Real)
(declare-fun b0_6 () Real)
(declare-fun b1_6 () Real)
(declare-fun b2_6 () Real)
(declare-fun b3_6 () Real)

(declare-fun qi_6 () Real)
(declare-fun q0_6 () Real)
(declare-fun q1_6 () Real)
(declare-fun q2_6 () Real)
(declare-fun q3_6 () Real)

(declare-fun t0_6 () Real)
(declare-fun t1_6 () Real)
(declare-fun t2_6 () Real)
(declare-fun t3_6 () Real)

;counterexample
(declare-fun bc_6 () Real)
(declare-fun qc_6 () Real)

(assert(>= t0_6 0))
(assert(>= t1_6 0))
(assert(>= t2_6 0))
(assert(>= t3_6 0))
(assert (<= bi_6 100))
(assert (<= b0_6 100))
(assert (<= b1_6 100))
(assert (<= b2_6 100))
(assert (<= b3_6 100))
(assert (>= qi_6 0))
(assert (>= q0_6 0))
(assert (>= q1_6 0))
(assert (>= q2_6 0))
(assert (>= q3_6 0))
(assert (<= x0_6 10))
(assert (<= x1_6 10))
(assert (<= x2_6 10))
(assert (<= x3_6 10))
(assert (>= x0_6 0))
(assert (>= x1_6 0))
(assert (>= x2_6 0))
(assert (>= x3_6 0))

;charging
(assert(= x0_6 0))
(assert(= b0_6 (+ bi_6 (* battery_charging_rate t0_6))))
(assert(= q0_6 (+ qi_6 (* queue_data_rate t0_6))))
;program: charge till battery >= 20
(assert (=> (>= bi_6 p2) (= b0_6 bi_6)))
(assert (or (=> (< bi_6 p2) (= b0_6 p2)) (= q0_6 100)))

;flying to D
(assert(= x1_6 10))
(assert(= x1_6 (+ x0_6 (* drone_velocity t1_6))))
(assert(= b1_6 (- b0_6 (* battery_discharge_rate_fly t1_6))))
(assert(= q1_6 (+ q0_6 (* queue_data_rate t1_6))))

;emptying queue
(assert(= x2_6 10))
(assert(= q2_6 (- q1_6 (* queue_upload_rate t2_6))))
(assert(= b2_6 (- b1_6 (* battery_discharge_rate_hover t2_6))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_6 p3) (= b2_6 p3)) (= q2_6 0)))
(assert (=> (<= b1_6 p3) (= b2_6 b1_6)))

;flying back
(assert(= x3_6 0))
(assert(= x3_6 (- x2_6 (* drone_velocity t3_6))))
(assert(= q3_6 (+ q2_6 (* queue_data_rate t3_6))))
(assert(= b3_6 (- b2_6 (* battery_discharge_rate_fly t3_6))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_6 10.01357078126485) (= qc_6 40.47329622237658))) here
(assert (and (= bc_6 10.01357078126485) (= qc_6 40.47329622237658)))

(assert (and (= bi_6 bc_6) (= qi_6 qc_6)))
(assert (=> (and (>= bi_6 p0) (<= qi_6 p1)) (and (> b0_6 0) (> b1_6 0) (> b2_6 0) (> b3_6 0) (< q0_6 100) (< q1_6 100) (< q2_6 100) (< q3_6 100) (and (>= b3_6 p0) (<= q3_6 p1)))))

(declare-fun x0_5 () Real)
(declare-fun x1_5 () Real)
(declare-fun x2_5 () Real)
(declare-fun x3_5 () Real)

(declare-fun bi_5 () Real)
(declare-fun b0_5 () Real)
(declare-fun b1_5 () Real)
(declare-fun b2_5 () Real)
(declare-fun b3_5 () Real)

(declare-fun qi_5 () Real)
(declare-fun q0_5 () Real)
(declare-fun q1_5 () Real)
(declare-fun q2_5 () Real)
(declare-fun q3_5 () Real)

(declare-fun t0_5 () Real)
(declare-fun t1_5 () Real)
(declare-fun t2_5 () Real)
(declare-fun t3_5 () Real)

;counterexample
(declare-fun bc_5 () Real)
(declare-fun qc_5 () Real)

(assert(>= t0_5 0))
(assert(>= t1_5 0))
(assert(>= t2_5 0))
(assert(>= t3_5 0))
(assert (<= bi_5 100))
(assert (<= b0_5 100))
(assert (<= b1_5 100))
(assert (<= b2_5 100))
(assert (<= b3_5 100))
(assert (>= qi_5 0))
(assert (>= q0_5 0))
(assert (>= q1_5 0))
(assert (>= q2_5 0))
(assert (>= q3_5 0))
(assert (<= x0_5 10))
(assert (<= x1_5 10))
(assert (<= x2_5 10))
(assert (<= x3_5 10))
(assert (>= x0_5 0))
(assert (>= x1_5 0))
(assert (>= x2_5 0))
(assert (>= x3_5 0))

;charging
(assert(= x0_5 0))
(assert(= b0_5 (+ bi_5 (* battery_charging_rate t0_5))))
(assert(= q0_5 (+ qi_5 (* queue_data_rate t0_5))))
;program: charge till battery >= 20
(assert (=> (>= bi_5 p2) (= b0_5 bi_5)))
(assert (or (=> (< bi_5 p2) (= b0_5 p2)) (= q0_5 100)))

;flying to D
(assert(= x1_5 10))
(assert(= x1_5 (+ x0_5 (* drone_velocity t1_5))))
(assert(= b1_5 (- b0_5 (* battery_discharge_rate_fly t1_5))))
(assert(= q1_5 (+ q0_5 (* queue_data_rate t1_5))))

;emptying queue
(assert(= x2_5 10))
(assert(= q2_5 (- q1_5 (* queue_upload_rate t2_5))))
(assert(= b2_5 (- b1_5 (* battery_discharge_rate_hover t2_5))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_5 p3) (= b2_5 p3)) (= q2_5 0)))
(assert (=> (<= b1_5 p3) (= b2_5 b1_5)))

;flying back
(assert(= x3_5 0))
(assert(= x3_5 (- x2_5 (* drone_velocity t3_5))))
(assert(= q3_5 (+ q2_5 (* queue_data_rate t3_5))))
(assert(= b3_5 (- b2_5 (* battery_discharge_rate_fly t3_5))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_5 6.107810141459485e-4) (= qc_5 6.806907628672157))) here
(assert (and (= bc_5 6.107810141459485e-4) (= qc_5 6.806907628672157)))

(assert (and (= bi_5 bc_5) (= qi_5 qc_5)))
(assert (=> (and (>= bi_5 p0) (<= qi_5 p1)) (and (> b0_5 0) (> b1_5 0) (> b2_5 0) (> b3_5 0) (< q0_5 100) (< q1_5 100) (< q2_5 100) (< q3_5 100) (and (>= b3_5 p0) (<= q3_5 p1)))))

(declare-fun x0_4 () Real)
(declare-fun x1_4 () Real)
(declare-fun x2_4 () Real)
(declare-fun x3_4 () Real)

(declare-fun bi_4 () Real)
(declare-fun b0_4 () Real)
(declare-fun b1_4 () Real)
(declare-fun b2_4 () Real)
(declare-fun b3_4 () Real)

(declare-fun qi_4 () Real)
(declare-fun q0_4 () Real)
(declare-fun q1_4 () Real)
(declare-fun q2_4 () Real)
(declare-fun q3_4 () Real)

(declare-fun t0_4 () Real)
(declare-fun t1_4 () Real)
(declare-fun t2_4 () Real)
(declare-fun t3_4 () Real)

;counterexample
(declare-fun bc_4 () Real)
(declare-fun qc_4 () Real)

(assert(>= t0_4 0))
(assert(>= t1_4 0))
(assert(>= t2_4 0))
(assert(>= t3_4 0))
(assert (<= bi_4 100))
(assert (<= b0_4 100))
(assert (<= b1_4 100))
(assert (<= b2_4 100))
(assert (<= b3_4 100))
(assert (>= qi_4 0))
(assert (>= q0_4 0))
(assert (>= q1_4 0))
(assert (>= q2_4 0))
(assert (>= q3_4 0))
(assert (<= x0_4 10))
(assert (<= x1_4 10))
(assert (<= x2_4 10))
(assert (<= x3_4 10))
(assert (>= x0_4 0))
(assert (>= x1_4 0))
(assert (>= x2_4 0))
(assert (>= x3_4 0))

;charging
(assert(= x0_4 0))
(assert(= b0_4 (+ bi_4 (* battery_charging_rate t0_4))))
(assert(= q0_4 (+ qi_4 (* queue_data_rate t0_4))))
;program: charge till battery >= 20
(assert (=> (>= bi_4 p2) (= b0_4 bi_4)))
(assert (or (=> (< bi_4 p2) (= b0_4 p2)) (= q0_4 100)))

;flying to D
(assert(= x1_4 10))
(assert(= x1_4 (+ x0_4 (* drone_velocity t1_4))))
(assert(= b1_4 (- b0_4 (* battery_discharge_rate_fly t1_4))))
(assert(= q1_4 (+ q0_4 (* queue_data_rate t1_4))))

;emptying queue
(assert(= x2_4 10))
(assert(= q2_4 (- q1_4 (* queue_upload_rate t2_4))))
(assert(= b2_4 (- b1_4 (* battery_discharge_rate_hover t2_4))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_4 p3) (= b2_4 p3)) (= q2_4 0)))
(assert (=> (<= b1_4 p3) (= b2_4 b1_4)))

;flying back
(assert(= x3_4 0))
(assert(= x3_4 (- x2_4 (* drone_velocity t3_4))))
(assert(= q3_4 (+ q2_4 (* queue_data_rate t3_4))))
(assert(= b3_4 (- b2_4 (* battery_discharge_rate_fly t3_4))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_4 10.01357078126485) (= qc_4 7.013570781264848))) here
(assert (and (= bc_4 10.01357078126485) (= qc_4 7.013570781264848)))

(assert (and (= bi_4 bc_4) (= qi_4 qc_4)))
(assert (=> (and (>= bi_4 p0) (<= qi_4 p1)) (and (> b0_4 0) (> b1_4 0) (> b2_4 0) (> b3_4 0) (< q0_4 100) (< q1_4 100) (< q2_4 100) (< q3_4 100) (and (>= b3_4 p0) (<= q3_4 p1)))))

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
(assert (<= x0_3 10))
(assert (<= x1_3 10))
(assert (<= x2_3 10))
(assert (<= x3_3 10))
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
(assert(= x1_3 10))
(assert(= x1_3 (+ x0_3 (* drone_velocity t1_3))))
(assert(= b1_3 (- b0_3 (* battery_discharge_rate_fly t1_3))))
(assert(= q1_3 (+ q0_3 (* queue_data_rate t1_3))))

;emptying queue
(assert(= x2_3 10))
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
; Add (assert (and (= bc_3 10.00703613576722) (= qc_3 7.006854955703473))) here
(assert (and (= bc_3 10.00703613576722) (= qc_3 7.006854955703473)))

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
(assert (<= x0_2 10))
(assert (<= x1_2 10))
(assert (<= x2_2 10))
(assert (<= x3_2 10))
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
(assert(= x1_2 10))
(assert(= x1_2 (+ x0_2 (* drone_velocity t1_2))))
(assert(= b1_2 (- b0_2 (* battery_discharge_rate_fly t1_2))))
(assert(= q1_2 (+ q0_2 (* queue_data_rate t1_2))))

;emptying queue
(assert(= x2_2 10))
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
; Add (assert (and (= bc_2 10.0) (= qc_2 6.999986022721044))) here
(assert (and (= bc_2 10.0) (= qc_2 6.999986022721044)))

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
(assert (<= x0_1 10))
(assert (<= x1_1 10))
(assert (<= x2_1 10))
(assert (<= x3_1 10))
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
(assert(= x1_1 10))
(assert(= x1_1 (+ x0_1 (* drone_velocity t1_1))))
(assert(= b1_1 (- b0_1 (* battery_discharge_rate_fly t1_1))))
(assert(= q1_1 (+ q0_1 (* queue_data_rate t1_1))))

;emptying queue
(assert(= x2_1 10))
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
; Add (assert (and (= bc_1 10.0) (= qc_1 49.0))) here
(assert (and (= bc_1 10.0) (= qc_1 49.0)))

(assert (and (= bi_1 bc_1) (= qi_1 qc_1)))
(assert (=> (and (>= bi_1 p0) (<= qi_1 p1)) (and (> b0_1 0) (> b1_1 0) (> b2_1 0) (> b3_1 0) (< q0_1 100) (< q1_1 100) (< q2_1 100) (< q3_1 100) (and (>= b3_1 p0) (<= q3_1 p1)))))



(check-sat)
(exit)
