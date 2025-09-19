; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(synth-fun qm-choose((x Int)(y Int)(z Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y z 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(constraint (= (qm-choose x y z ) (ite (and (< y x) (< x z)) 1 0)))
(check-synth)


