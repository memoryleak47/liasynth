; printing sygus problem  

(set-logic LIA)
(declare-var x1 Int)

(declare-var x2 Int)

(declare-var x3 Int)

(declare-var x4 Int)

(declare-var x5 Int)

(declare-var x6 Int)

(declare-var x7 Int)

(declare-var x8 Int)

(declare-var x9 Int)

(synth-fun __SYNTHFUN_max9((x1 Int)(x2 Int)(x3 Int)(x4 Int)(x5 Int)(x6 Int)(x7 Int)(x8 Int)(x9 Int)) Int
((Start Int)(StartBool Bool))
((Start Int (x1 x2 x3 x4 x5 x6 x7 x8 x9 0 1 (+ Start Start) (- Start Start) (ite StartBool Start Start) ))
(StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start) ))
)
)

(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x1))
(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x2))
(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x3))
(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x4))
(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x5))
(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x6))
(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x7))
(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x8))
(constraint (>= (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) x9))
(constraint (or (= x1 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )) (or (= x2 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )) (or (= x3 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )) (or (= x4 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )) (or (= x5 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )) (or (= x6 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )) (or (= x7 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )) (or (= x8 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )) (= x9 (__SYNTHFUN_max9 x1 x2 x3 x4 x5 x6 x7 x8 x9 )))))))))))
(check-synth)


