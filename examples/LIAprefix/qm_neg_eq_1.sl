; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(synth-fun __SYNTHFUN_qm-foo((x Int)) Int
((Start Int))
((Start Int (x 0 1 (- Start Start) (qm Start Start ) ))
)
)

(constraint (= (__SYNTHFUN_qm-foo x ) (ite (<= x 0) 1 0)))
(check-synth)


