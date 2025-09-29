; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(synth-fun __SYNTHFUN_max2((x Int)(y Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (>= (__SYNTHFUN_max2 x y ) x))
(constraint (>= (__SYNTHFUN_max2 x y ) y))
(constraint (or (= x (__SYNTHFUN_max2 x y )) (= y (__SYNTHFUN_max2 x y ))))
(check-synth)


