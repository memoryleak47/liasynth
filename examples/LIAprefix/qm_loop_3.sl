; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(synth-fun __SYNTHFUN_qm-multi-loop((x Int)(y Int)(z Int)) Int
((Start Int))
((Start Int (x y z 0 1 3 (- Start Start) (+ Start Start) (qm Start Start ) ))
)
)

(constraint (or (or (or (< x 0) (< y 0)) (< z 0)) (= (__SYNTHFUN_qm-multi-loop x y z ) (ite (and (= z 0) (= y 0)) (ite (= x 0) 3 (- x 1)) x))))
(check-synth)


