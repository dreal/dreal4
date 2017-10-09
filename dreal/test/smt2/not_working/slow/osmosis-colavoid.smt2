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
(declare-fun Y1 () Real)
(declare-fun Y2 () Real)
(declare-fun H1 () Real)
(declare-fun H2 () Real)
(declare-fun y1_1 () Real)
(declare-fun y2_1 () Real)
(declare-fun h1_1 () Real)
(declare-fun h2_1 () Real)
(declare-fun sin1_1 () Real)
(declare-fun cos1_1 () Real)
(declare-fun sin2_1 () Real)
(declare-fun cos2_1 () Real)
(declare-fun v1_1 () Real)
(declare-fun v2_1 () Real)
(declare-fun a0_1 () Real)
(declare-fun a1_1 () Real)
(declare-fun a_1 () Real)
(declare-fun b_1 () Real)
(declare-fun c0_1 () Real)
(declare-fun c1_1 () Real)
(declare-fun c_1 () Real)
(declare-fun q_1 () Real)
(assert (>= Y1 0))
(assert (<= Y1 50))
(assert (>= Y2 0))
(assert (<= Y2 50))
(assert (>= H1 -90))
(assert (<= H1 90))
(assert (>= H2 90))
(assert (<= H2 270))
(assert (= y1_1 Y1))
(assert (= y2_1 Y2))
(assert (= h1_1 H1))
(assert (= h2_1 H2))
(assert (= sin1_1 (sin (/ (* h1_1 3.141593) 180))))
(assert (= cos1_1 (cos (/ (* h1_1 3.141593) 180))))
(assert (= sin2_1 (sin (/ (* h2_1 3.141593) 180))))
(assert (= cos2_1 (cos (/ (* h2_1 3.141593) 180))))
(assert (= v1_1 1))
(assert (= v2_1 1))
(assert (= a0_1 (- (* v1_1 cos1_1) (* v2_1 cos2_1))))
(assert (= a1_1 (- (* v1_1 sin1_1) (* v2_1 sin2_1))))
(assert (= a_1 (+ (* a0_1 a0_1) (* a1_1 a1_1))))
(assert (= b_1 (+ (* -100.000000 (- (* v1_1 cos1_1) (* v2_1 cos2_1))) (*  2 (- y1_1 y2_1) (- (* v1_1 sin1_1) (* v2_1 sin2_1))))))
(assert (= c0_1 -50.000000))
(assert (= c1_1 (- y1_1 y2_1)))
(assert (= c_1 (+ (* c0_1 c0_1) (* c1_1 c1_1))))
(assert (= q_1 (- (* b_1 b_1) (*  4 a_1 (- c_1 1.000000)))))
(assert (not (< q_1 0)))
(check-sat)
(exit)
