; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(declare-var w Int)

(synth-fun __SYNTHFUN_max4((x Int)(y Int)(z Int)(w Int)) Int
((Start Int)(StartBool Bool))
((Start Int (x y z w 0 1 (+ Start Start) (- Start Start) (ite StartBool Start Start) ))
(StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start) ))
)
)

(constraint (>= (__SYNTHFUN_max4 x y z w ) x))
(constraint (>= (__SYNTHFUN_max4 x y z w ) y))
(constraint (>= (__SYNTHFUN_max4 x y z w ) z))
(constraint (>= (__SYNTHFUN_max4 x y z w ) w))
(constraint (or (= x (__SYNTHFUN_max4 x y z w )) (or (= y (__SYNTHFUN_max4 x y z w )) (or (= z (__SYNTHFUN_max4 x y z w )) (= w (__SYNTHFUN_max4 x y z w ))))))
(check-synth)


