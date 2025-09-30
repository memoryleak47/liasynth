; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(synth-fun __SYNTHFUN_f((x Int)) Int
((Start Int)(StartBool Bool))
((Start Int (x 0 10 20 30 40 50 60 70 80 90 100 (+ Start Start) (- Start Start) (ite StartBool Start Start) ))
(StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start) ))
)
)

(constraint (= (__SYNTHFUN_f 0 ) 0))
(constraint (= (__SYNTHFUN_f 1 ) 10))
(constraint (= (__SYNTHFUN_f 2 ) 20))
(constraint (= (__SYNTHFUN_f 3 ) 30))
(constraint (= (__SYNTHFUN_f 4 ) 40))
(constraint (= (__SYNTHFUN_f 5 ) 50))
(constraint (or (and (> x 5) (= (__SYNTHFUN_f x ) x)) (<= x 5)))
(check-synth)


