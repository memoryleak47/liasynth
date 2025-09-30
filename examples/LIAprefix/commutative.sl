; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(synth-fun __SYNTHFUN_comm((x Int)(y Int)) Int
((Start Int))
((Start Int (x y (+ Start Start) (- Start Start) ))
)
)

(constraint (= (__SYNTHFUN_comm x y ) (__SYNTHFUN_comm y x )))
(check-synth)


