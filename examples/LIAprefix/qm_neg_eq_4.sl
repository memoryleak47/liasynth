; printing sygus problem  

(set-logic LIA)
(declare-var w Int)

(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(synth-fun __SYNTHFUN_qm-foo((w Int)(x Int)(y Int)(z Int)) Int
((Start Int))
((Start Int (w x y z 0 1 (- Start Start) (qm Start Start ) ))
)
)

(constraint (= (__SYNTHFUN_qm-foo w x y z ) (ite (and (<= w 0) (and (<= x 0) (and (<= y 0) (<= z 0)))) 1 0)))
(check-synth)


