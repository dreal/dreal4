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
(declare-fun T11 () Real)
(declare-fun T21 () Real)
(declare-fun T12 () Real)
(declare-fun T22 () Real)
(declare-fun T13 () Real)
(declare-fun T23 () Real)
(declare-fun t1_1 () Real)
(declare-fun t2_1 () Real)
(declare-fun _C0_ () Bool)
(declare-fun t1_2 () Real)
(declare-fun t2_2 () Real)
(declare-fun _C1_ () Bool)
(declare-fun t1_3 () Real)
(declare-fun t2_3 () Real)
(assert (>= T11 0))
(assert (<= T11 1))
(assert (>= T21 0))
(assert (<= T21 1))
(assert (>= T12 0))
(assert (<= T12 1))
(assert (>= T22 0))
(assert (<= T22 1))
(assert (>= T13 0))
(assert (<= T13 1))
(assert (>= T23 0))
(assert (<= T23 1))
(assert (= t1_1 T11))
(assert (= t2_1 T21))
(assert (= _C0_ (< (abs (- t1_1 t2_1)) 0.010000)))
(assert (or (not _C0_) (= t1_2 (+ t1_1  0.025000 (* T12 2)))))
(assert (or (not _C0_) (= t2_2 (+ t2_1  0.025000 (* T22 2)))))
(assert (or _C0_ (= t1_2 t1_1)))
(assert (or _C0_ (= t2_2 t2_1)))
(assert (= _C1_ (< (abs (- t1_2 t2_2)) 0.010000)))
(assert (or (not _C1_) (= t1_3 (+ t1_2  0.025000 (* T13 4)))))
(assert (or (not _C1_) (= t2_3 (+ t2_2  0.025000 (* T23 4)))))
(assert (or _C1_ (= t1_3 t1_2)))
(assert (or _C1_ (= t2_3 t2_2)))
(assert (not (and  (> (abs (- t1_3 t2_3)) 0.010000) (< t1_3 4.000000) (< t2_3 4.000000))))
(check-sat)
(exit)
