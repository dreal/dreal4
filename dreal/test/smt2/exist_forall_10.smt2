;; -(y + 47) * sin(sqrt(abs(x / 2 + y + 47))) - x * sin(sqrt(abs(x - y - 47)));
;; EggHolder function
(set-logic QF_NRA)
(declare-fun x1 () Real [-512, 512])
(declare-fun y1 () Real [-512, 512])
(declare-fun z () Real)
(assert
 (forall ((x2 Real [-512, 512])
	  (y2 Real [-512, 512]))
         (<=
	  z
	  (-
	   (* -1
	      (+ y2 47)
	      (sin (sqrt (abs (+ (/ x2 2)
				 y2
				 47)))))
	   (* x2
	      (sin (sqrt (abs (- x2
				 y2
				 47)))))))))
(assert (= z
	   (-
	    (* -1
	       (+ y1 47)
	       (sin (sqrt (abs (+ (/ x1 2)
				  y1
				  47)))))
	    (* x1
	       (sin (sqrt (abs (- x1
				  y1
				  47))))))))
(check-sat)
(exit)


