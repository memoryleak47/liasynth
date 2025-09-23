; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var ax Int)

(declare-var ay Int)

(declare-var bx Int)

(declare-var by Int)

(define-fun qm ((a Int)(b Int)) Int
 (ite (< a 0) b a))

(synth-fun qm-foo((x Int)(y Int)(ax Int)(ay Int)(bx Int)(by Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y ax ay bx by 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (= (qm-foo x y ax ay bx by ) (let ((adx (- x ax)) (ady (- y ay)) (bdx (- x bx)) (bdy (- y by))) (let ((aax (ite (< adx 0) (- 0 adx) adx)) (aay (ite (< ady 0) (- 0 ady) ady)) (bax (ite (< bdx 0) (- 0 bdx) bdx)) (bay (ite (< bdy 0) (- 0 bdy) bdy))) (ite (< (+ aax aay) (+ bax bay)) 1 0)))))
(check-synth)


