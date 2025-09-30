; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(synth-fun __SYNTHFUN_f((x Int)(y Int)) Int
((Start Int)(StartBool Bool))
((Start Int (x y 0 1 (- 1) 2 (- 2) (+ Start Start) (- Start Start) (ite StartBool Start Start) ))
(StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start) ))
)
)

(constraint (or (and (= x y) (= (__SYNTHFUN_f x y ) 0)) (or (and (> x y) (= (__SYNTHFUN_f x y ) 1)) (= (__SYNTHFUN_f x y ) (- 1)))))
(check-synth)


