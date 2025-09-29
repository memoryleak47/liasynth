; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(synth-fun __SYNTHFUN_f((x Int)(y Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (or (and (= x y) (= (__SYNTHFUN_f x y ) 0)) (or (and (> x y) (= (__SYNTHFUN_f x y ) 1)) (= (__SYNTHFUN_f x y ) (- 1)))))
(check-synth)


