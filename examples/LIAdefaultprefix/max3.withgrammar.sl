; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(synth-fun __SYNTHFUN_max3((x Int)(y Int)(z Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y z 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (>= (__SYNTHFUN_max3 x y z ) x))
(constraint (>= (__SYNTHFUN_max3 x y z ) y))
(constraint (>= (__SYNTHFUN_max3 x y z ) z))
(constraint (or (= x (__SYNTHFUN_max3 x y z )) (or (= y (__SYNTHFUN_max3 x y z )) (= z (__SYNTHFUN_max3 x y z )))))
(check-synth)


