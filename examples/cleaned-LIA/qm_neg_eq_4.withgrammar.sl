; printing sygus problem  

(set-logic LIA)
(declare-var w Int)

(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(synth-fun qm-foo((w Int)(x Int)(y Int)(z Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (w x y z 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (= (qm-foo w x y z ) (ite (and (<= w 0) (and (<= x 0) (and (<= y 0) (<= z 0)))) 1 0)))
(check-synth)


