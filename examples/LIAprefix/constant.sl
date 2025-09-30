; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(synth-fun __SYNTHFUN_constant((x Int)) Int
((Start Int))
((Start Int (x 0 1 (+ Start Start) (- Start Start) ))
)
)

(constraint (= (__SYNTHFUN_constant x ) (__SYNTHFUN_constant y )))
(check-synth)


