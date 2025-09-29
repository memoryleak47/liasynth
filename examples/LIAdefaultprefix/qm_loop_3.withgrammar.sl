; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(synth-fun __SYNTHFUN_qm-multi-loop((x Int)(y Int)(z Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y z 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (or (or (or (< x 0) (< y 0)) (< z 0)) (= (__SYNTHFUN_qm-multi-loop x y z ) (ite (and (= z 0) (= y 0)) (ite (= x 0) 3 (- x 1)) x))))
(check-synth)


