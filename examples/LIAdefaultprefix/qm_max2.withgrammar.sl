; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(synth-fun __SYNTHFUN_qm-foo((x Int)(y Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (= (__SYNTHFUN_qm-foo x y ) (ite (<= x y) y x)))
(check-synth)


