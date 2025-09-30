; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(synth-fun __SYNTHFUN_max3((x Int)(y Int)(z Int)) Int
((Start Int)(StartBool Bool))
((Start Int (x y z 0 1 (+ Start Start) (- Start Start) (ite StartBool Start Start) ))
(StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start) ))
)
)

(constraint (>= (__SYNTHFUN_max3 x y z ) x))
(constraint (>= (__SYNTHFUN_max3 x y z ) y))
(constraint (>= (__SYNTHFUN_max3 x y z ) z))
(constraint (or (= x (__SYNTHFUN_max3 x y z )) (or (= y (__SYNTHFUN_max3 x y z )) (= z (__SYNTHFUN_max3 x y z )))))
(check-synth)


