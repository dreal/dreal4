;; Copyright (c) 2015 Carnegie Mellon University. All Rights Reserved.
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:
;; 
;; 1. Redistributions of source code must retain the above copyright
;; notice, this list of conditions and the following acknowledgments and
;; disclaimers.
;; 
;; 2. Redistributions in binary form must reproduce the above copyright
;; notice, this list of conditions and the following disclaimer in the
;; documentation and/or other materials provided with the distribution.
;; 
;; 3. The names "Carnegie Mellon University," "SEI" and/or "Software
;; Engineering Institute" shall not be used to endorse or promote
;; products derived from this software without prior written
;; permission. For written permission, please contact
;; permission@sei.cmu.edu.
;; 
;; 4. Products derived from this software may not be called "SEI" nor may
;; "SEI" appear in their names without prior written permission of
;; permission@sei.cmu.edu.
;; 
;; 5. Redistributions of any form whatsoever must retain the following
;; acknowledgment:
;; 
;; This material is based upon work funded and supported by the
;; Department of Defense under Contract No. FA8721-05-C-0003 with
;; Carnegie Mellon University for the operation of the Software
;; Engineering Institute, a federally funded research and development
;; center.
;; 
;; Any opinions, findings and conclusions or recommendations expressed in
;; this material are those of the author(s) and do not necessarily
;; reflect the views of the United States Department of Defense.
;; 
;; NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
;; INSTITUTE MATERIAL IS FURNISHED ON AN AS-IS BASIS. CARNEGIE
;; MELLON UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
;; IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
;; FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
;; OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
;; MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
;; TRADEMARK, OR COPYRIGHT INFRINGEMENT.
;; 
;; This material has been approved for public release and unlimited distribution.
;; 
;; DM-0002403
;; 
(set-logic QF_NRA)
(declare-fun v0 () Real)
(declare-fun theta () Real)
(declare-fun v0_1 () Real)
(declare-fun theta_1 () Real)
(declare-fun vx_1 () Real)
(declare-fun vy_1 () Real)
(declare-fun x_1 () Real)
(declare-fun t_1 () Real)
(declare-fun bounces_1 () Int)
(declare-fun _C0_ () Bool)
(declare-fun t_2 () Real)
(declare-fun x_2 () Real)
(declare-fun vx_2 () Real)
(declare-fun vy_2 () Real)
(declare-fun bounces_2 () Int)
(declare-fun _C1_ () Bool)
(declare-fun t_3 () Real)
(declare-fun x_3 () Real)
(declare-fun vx_3 () Real)
(declare-fun vy_3 () Real)
(declare-fun bounces_3 () Int)
(declare-fun _C2_ () Bool)
(declare-fun t_4 () Real)
(declare-fun x_4 () Real)
(declare-fun vx_4 () Real)
(declare-fun vy_4 () Real)
(declare-fun bounces_4 () Int)
(declare-fun _C3_ () Bool)
(declare-fun t_5 () Real)
(declare-fun x_5 () Real)
(declare-fun vx_5 () Real)
(declare-fun vy_5 () Real)
(declare-fun bounces_5 () Int)
(declare-fun _C4_ () Bool)
(declare-fun t_6 () Real)
(declare-fun x_6 () Real)
(declare-fun vx_6 () Real)
(declare-fun vy_6 () Real)
(declare-fun bounces_6 () Int)
(declare-fun _C5_ () Bool)
(declare-fun t_7 () Real)
(declare-fun x_7 () Real)
(declare-fun vx_7 () Real)
(declare-fun vy_7 () Real)
(declare-fun bounces_7 () Int)
(assert (>= v0 1))
(assert (<= v0 10))
(assert (>= theta 1))
(assert (<= theta 89))
(assert (= v0_1 v0))
(assert (= theta_1 (/ (* theta 3.141593) 180.000000)))
(assert (= vx_1 (* v0_1 (cos theta_1))))
(assert (= vy_1 (* v0_1 (sin theta_1))))
(assert (= x_1 0.000000))
(assert (= t_1 0))
(assert (= bounces_1 0))
(assert (= _C0_ (and  (< x_1 10.050000) (> (abs (- x_1 10.000000)) 0.050000) (< bounces_1 6))))
(assert (or (not _C0_) (= t_2 (/ (* (pow 2 0.500000) vy_1) 9.800000))))
(assert (or (not _C0_) (= x_2 (+ x_1 (* vx_1 t_2)))))
(assert (or (not _C0_) (= vx_2 (* vx_1 0.900000))))
(assert (or (not _C0_) (= vy_2 (* vy_1 0.900000))))
(assert (or (not _C0_) (= bounces_2 (+ bounces_1 1))))
(assert (or _C0_ (= bounces_2 bounces_1)))
(assert (or _C0_ (= vy_2 vy_1)))
(assert (or _C0_ (= x_2 x_1)))
(assert (or _C0_ (= t_2 t_1)))
(assert (or _C0_ (= vx_2 vx_1)))
(assert (= _C1_ (and  (< x_2 10.050000) (> (abs (- x_2 10.000000)) 0.050000) (< bounces_2 6))))
(assert (or (not _C1_) (= t_3 (/ (* (pow 2 0.500000) vy_2) 9.800000))))
(assert (or (not _C1_) (= x_3 (+ x_2 (* vx_2 t_3)))))
(assert (or (not _C1_) (= vx_3 (* vx_2 0.900000))))
(assert (or (not _C1_) (= vy_3 (* vy_2 0.900000))))
(assert (or (not _C1_) (= bounces_3 (+ bounces_2 1))))
(assert (or _C1_ (= bounces_3 bounces_2)))
(assert (or _C1_ (= vy_3 vy_2)))
(assert (or _C1_ (= x_3 x_2)))
(assert (or _C1_ (= t_3 t_2)))
(assert (or _C1_ (= vx_3 vx_2)))
(assert (= _C2_ (and  (< x_3 10.050000) (> (abs (- x_3 10.000000)) 0.050000) (< bounces_3 6))))
(assert (or (not _C2_) (= t_4 (/ (* (pow 2 0.500000) vy_3) 9.800000))))
(assert (or (not _C2_) (= x_4 (+ x_3 (* vx_3 t_4)))))
(assert (or (not _C2_) (= vx_4 (* vx_3 0.900000))))
(assert (or (not _C2_) (= vy_4 (* vy_3 0.900000))))
(assert (or (not _C2_) (= bounces_4 (+ bounces_3 1))))
(assert (or _C2_ (= bounces_4 bounces_3)))
(assert (or _C2_ (= vy_4 vy_3)))
(assert (or _C2_ (= x_4 x_3)))
(assert (or _C2_ (= t_4 t_3)))
(assert (or _C2_ (= vx_4 vx_3)))
(assert (= _C3_ (and  (< x_4 10.050000) (> (abs (- x_4 10.000000)) 0.050000) (< bounces_4 6))))
(assert (or (not _C3_) (= t_5 (/ (* (pow 2 0.500000) vy_4) 9.800000))))
(assert (or (not _C3_) (= x_5 (+ x_4 (* vx_4 t_5)))))
(assert (or (not _C3_) (= vx_5 (* vx_4 0.900000))))
(assert (or (not _C3_) (= vy_5 (* vy_4 0.900000))))
(assert (or (not _C3_) (= bounces_5 (+ bounces_4 1))))
(assert (or _C3_ (= bounces_5 bounces_4)))
(assert (or _C3_ (= vy_5 vy_4)))
(assert (or _C3_ (= x_5 x_4)))
(assert (or _C3_ (= t_5 t_4)))
(assert (or _C3_ (= vx_5 vx_4)))
(assert (= _C4_ (and  (< x_5 10.050000) (> (abs (- x_5 10.000000)) 0.050000) (< bounces_5 6))))
(assert (or (not _C4_) (= t_6 (/ (* (pow 2 0.500000) vy_5) 9.800000))))
(assert (or (not _C4_) (= x_6 (+ x_5 (* vx_5 t_6)))))
(assert (or (not _C4_) (= vx_6 (* vx_5 0.900000))))
(assert (or (not _C4_) (= vy_6 (* vy_5 0.900000))))
(assert (or (not _C4_) (= bounces_6 (+ bounces_5 1))))
(assert (or _C4_ (= bounces_6 bounces_5)))
(assert (or _C4_ (= vy_6 vy_5)))
(assert (or _C4_ (= x_6 x_5)))
(assert (or _C4_ (= t_6 t_5)))
(assert (or _C4_ (= vx_6 vx_5)))
(assert (= _C5_ (and  (< x_6 10.050000) (> (abs (- x_6 10.000000)) 0.050000) (< bounces_6 6))))
(assert (or (not _C5_) (= t_7 (/ (* (pow 2 0.500000) vy_6) 9.800000))))
(assert (or (not _C5_) (= x_7 (+ x_6 (* vx_6 t_7)))))
(assert (or (not _C5_) (= vx_7 (* vx_6 0.900000))))
(assert (or (not _C5_) (= vy_7 (* vy_6 0.900000))))
(assert (or (not _C5_) (= bounces_7 (+ bounces_6 1))))
(assert (or _C5_ (= bounces_7 bounces_6)))
(assert (or _C5_ (= vy_7 vy_6)))
(assert (or _C5_ (= x_7 x_6)))
(assert (or _C5_ (= t_7 t_6)))
(assert (or _C5_ (= vx_7 vx_6)))
(assert (not (> (abs (- x_7 10.000000)) 0.050000)))
(check-sat)
(exit)
