; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(synth-fun qm-foo((x Int)(y Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(constraint (= (qm-foo x y ) (ite (and (< x 0) (< y 0)) 1 0)))
(check-synth)


