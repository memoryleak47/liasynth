; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(declare-var w Int)

(declare-var u Int)

(synth-fun __SYNTHFUN_max5((x Int)(y Int)(z Int)(w Int)(u Int)) Int
((Start Int)(StartBool Bool))
((Start Int (x y z w u 0 1 (+ Start Start) (- Start Start) (ite StartBool Start Start) ))
(StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start) ))
)
)

(constraint (>= (__SYNTHFUN_max5 x y z w u ) x))
(constraint (>= (__SYNTHFUN_max5 x y z w u ) y))
(constraint (>= (__SYNTHFUN_max5 x y z w u ) z))
(constraint (>= (__SYNTHFUN_max5 x y z w u ) w))
(constraint (>= (__SYNTHFUN_max5 x y z w u ) u))
(constraint (or (= x (__SYNTHFUN_max5 x y z w u )) (or (= y (__SYNTHFUN_max5 x y z w u )) (or (= z (__SYNTHFUN_max5 x y z w u )) (or (= w (__SYNTHFUN_max5 x y z w u )) (= u (__SYNTHFUN_max5 x y z w u )))))))
(check-synth)


