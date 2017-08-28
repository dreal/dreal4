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
(declare-fun theta1 () Real)
(declare-fun theta2 () Real)
(declare-fun v1 () Real)
(declare-fun v2 () Real)
(declare-fun theta1_1 () Real)
(declare-fun theta2_1 () Real)
(declare-fun v1_1 () Real)
(declare-fun v2_1 () Real)
(declare-fun sin1_1 () Real)
(declare-fun sin2_1 () Real)
(declare-fun cos1_1 () Real)
(declare-fun cos2_1 () Real)
(declare-fun t_1 () Real)
(declare-fun x1_1 () Real)
(declare-fun x2_1 () Real)
(declare-fun y1_1 () Real)
(declare-fun y2_1 () Real)
(declare-fun minD2_1 () Real)
(assert (>= theta1 0.01))
(assert (<= theta1 1.56))
(assert (>= theta2 0.01))
(assert (<= theta2 1.56))
(assert (>= v1 0.01))
(assert (<= v1 10))
(assert (>= v2 0.01))
(assert (<= v2 10))
(assert (= theta1_1 theta1))
(assert (= theta2_1 theta2))
(assert (= v1_1 v1))
(assert (= v2_1 v2))
(assert (= sin1_1 (sin theta1_1)))
(assert (= sin2_1 (sin theta2_1)))
(assert (= cos1_1 (cos theta1_1)))
(assert (= cos2_1 (cos theta2_1)))
(assert (= t_1 (/ (* 10.000000 (+ (* v1_1 cos1_1) (* v2_1 cos2_1))) (+ (- (+   (*   cos1_1 cos1_1 v1_1 v1_1) (*    2 cos1_1 cos2_1 v1_1 v2_1) (*   cos2_1 cos2_1 v2_1 v2_1) (*   sin1_1 sin1_1 v1_1 v1_1)) (*    2 sin1_1 sin2_1 v1_1 v2_1)) (*   sin2_1 sin2_1 v2_1 v2_1)))))
(assert (= x1_1 (*  v1_1 cos1_1 t_1)))
(assert (= x2_1 (- 10.000000 (*  v2_1 cos2_1 t_1))))
(assert (= y1_1 (- (*  v1_1 sin1_1 t_1) (*  4.900000 t_1 t_1))))
(assert (= y2_1 (- (*  v2_1 sin2_1 t_1) (*  4.900000 t_1 t_1))))
(assert (= minD2_1 (+ (* (- x1_1 y2_1) (- x1_1 y2_1)) (* (- y1_1 y2_1) (- y1_1 y2_1)))))
(assert (not (> minD2_1 0.040000)))
(check-sat)
(exit)
