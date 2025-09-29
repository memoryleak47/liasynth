; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(synth-fun __SYNTHFUN_f((x Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
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


