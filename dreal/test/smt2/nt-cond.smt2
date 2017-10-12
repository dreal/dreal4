(set-logic QF_NRA)

; Generated variables

(declare-fun y_0 () Real)
(declare-fun y_1 () Real)
(declare-fun var_1_0 () Real)
(declare-fun var_1_1 () Real)
(declare-fun var_1_2 () Real)
(declare-fun var_1_3 () Real)
(declare-fun var_1_4 () Real)
(declare-fun var_1_5 () Real)
(declare-fun var_1_6 () Real)
(declare-fun var_1_7 () Real)
(declare-fun var_2_0 () Real)
(declare-fun var_2_1 () Real)
(declare-fun var_2_2 () Real)
(declare-fun var_2_3 () Real)
(declare-fun var_2_4 () Real)
(declare-fun var_2_5 () Real)
(declare-fun var_2_6 () Real)
(declare-fun var_2_7 () Real)
(declare-fun x_0 () Real)
(declare-fun x_1 () Real)

; Generated assertions

(assert (= var_2_0 (+ 0.796538770198822 (* -0.570923924446106 x_0) (* 0.46736636757850647 x_1))))
(assert (= var_2_1 (+ -0.2284362018108368 (* -3.359499216079712 x_0) (* -0.0386742502450943 x_1))))
(assert (= var_2_2 (+ -0.14343389868736267 (* 0.05246175080537796 x_0) (* 2.529650926589966 x_1))))
(assert (= var_2_3 (+ 0.7238969206809998 (* -0.3924175202846527 x_0) (* 0.5403934717178345 x_1))))
(assert (= var_2_4 (+ 0.8858605623245239 (* -0.5967410802841187 x_0) (* 0.5608729720115662 x_1))))
(assert (= var_2_5 (+ -0.08853857219219208 (* -0.024724101647734642 x_0) (* 1.7321099042892456 x_1))))
(assert (= var_2_6 (+ 0.822327733039856 (* -0.5400217771530151 x_0) (* 0.5341808795928955 x_1))))
(assert (= var_2_7 (+ 1.0181562900543213 (* -0.619328498840332 x_0) (* 0.7071459889411926 x_1))))
(assert (= var_1_0 (max 0 var_2_0)))
(assert (= var_1_1 (max 0 var_2_1)))
(assert (= var_1_2 (max 0 var_2_2)))
(assert (= var_1_3 (max 0 var_2_3)))
(assert (= var_1_4 (max 0 var_2_4)))
(assert (= var_1_5 (max 0 var_2_5)))
(assert (= var_1_6 (max 0 var_2_6)))
(assert (= var_1_7 (max 0 var_2_7)))
(assert (= y_0 (+ 0.45850253105163574 (* -1.6327966451644897 var_1_0) (* 2.1671383380889893 var_1_1) (* 1.4425779581069946 var_1_2) (* -1.4661110639572144 var_1_3) (* -1.19851815700531 var_1_4) (* 2.2534382343292236 var_1_5) (* -1.0836831331253052 var_1_6) (* -1.6426600217819214 var_1_7))))
(assert (= y_1 (+ -0.45850256085395813 (* 1.4750717878341675 var_1_0) (* -2.5883686542510986 var_1_1) (* -1.7981479167938232 var_1_2) (* 1.5283703804016113 var_1_3) (* 0.9260153770446777 var_1_4) (* -2.3773224353790283 var_1_5) (* 0.8808010220527649 var_1_6) (* 1.157231092453003 var_1_7))))

; My variables

(declare-fun radius () Real)

; My assertions

(assert (= radius (+ (^ x_0 2) (^ x_1 2))))

(assert (and (<= -1 x_0)   ; restrict input to box
             (<= x_0 1)
             (<= -1 x_1)
             (<= x_1 1)))

; Find misclassified points on the inside only
;(assert (and (> y_0 y_1)  ; classified as outside
;            (< radius 0.9125)))

; Find all misclassified points
(assert (or
    (and (> y_0 y_1)  ; classified as outside
        (< radius 0.9125))     ; 0.9125 unsat; with 0.925 this is delta-sat
    (and (< y_0 y_1)  ; classified as inside
        (> radius 1.19375))))  ; 1.19375 unsat; with 1.1875 this is delta-sat

(check-sat)
(exit)
