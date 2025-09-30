; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(synth-fun __SYNTHFUN_f((x Int)) Int
((Start Int)(StartBool Bool))
((Start Int (x 0 10 20 30 40 50 60 70 80 90 100 (+ Start Start) (- Start Start) (ite StartBool Start Start) ))
(StartBool Bool ((not StartBool) (= Start Start) ))
)
)

(constraint (= (__SYNTHFUN_f 0 ) 0))
(constraint (= (__SYNTHFUN_f 1 ) 10))
(constraint (= (__SYNTHFUN_f 2 ) 20))
(constraint (= (__SYNTHFUN_f 3 ) 30))
(constraint (= (__SYNTHFUN_f 4 ) 40))
(constraint (= (__SYNTHFUN_f 5 ) 50))
(constraint (= (__SYNTHFUN_f 6 ) 6))
(constraint (= (__SYNTHFUN_f 7 ) 7))
(constraint (= (__SYNTHFUN_f 8 ) 8))
(constraint (= (__SYNTHFUN_f 9 ) 9))
(constraint (= (__SYNTHFUN_f 10 ) 10))
(check-synth)


