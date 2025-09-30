; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(synth-fun __SYNTHFUN_qm-foo((x Int)(y Int)) Int
((Start Int))
((Start Int (x y 0 1 (- Start Start) (qm Start Start ) ))
)
)

(constraint (= (__SYNTHFUN_qm-foo x y ) (ite (and (< x 0) (< y 0)) 1 0)))
(check-synth)


