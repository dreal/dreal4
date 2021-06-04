(set-logic QF_NRA)


;--------------- SAMPLE CONTEXT FOR DESCRIBING THE BUG

(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(declare-fun e () Real)
(declare-fun f () Real)
(declare-fun Y () Real)


(assert (= a 8.768685282571274))
(assert (= b 29.761904761904763))
(assert (= c 5))
(assert (= d 15))
(assert (= e 0))
(assert (= f 10))
(assert (= Y 10))


(declare-fun Joker () Real)
(assert (= Joker 12.8313))


(define-fun absolute ( (val Real) ) Real
    (ite
        (>= val 0.0)
        val
        (- 0.0 val)
    )
)



(define-fun fun1 ( (x Real) ) Bool
    (<= (absolute (+ 10 (* -10 (- x a)))) Y)
)


;-------------  THE BUG/ISSUE

(declare-fun test_print1 () Bool)  ; test variable to print values
(assert
    (= test_print1
        (and (>= (+ a Joker) a) (<= (+ a Joker) b))
    )
)

;--- test_print1 EVALUATES TO TRUE


(declare-fun test_print2 () Bool)  ; test variable to print values
(assert
    (= test_print2
        (fun1 (+ a Joker))
    )
)

;--- test_print2 EVALUATES TO FALSE


(declare-fun test_print3 () Bool)  ; test variable to print values
(assert
    (= test_print3
        (and
            (and (>= (+ a Joker) a) (<= (+ a Joker) b)) ; equivalent to test_print1
            (fun1 (+ a Joker)) ; equivalent to test_print2
        )
    )
)

;--- test_print3, which is equivalent to the conjuction of test_print1 and test_print2 SHOULD EVALUATE TO FALSE, BUT IT EVALUATES TO TRUE !!!


(check-sat)
(get-model)
