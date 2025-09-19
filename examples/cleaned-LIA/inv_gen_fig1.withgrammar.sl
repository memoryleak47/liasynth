; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var x1 Int)

(declare-var y1 Int)

(synth-fun inv((x Int)(y Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (x y 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (or (not (= 0 (+ x 50))) (inv x y )))
(constraint (or (not (and (and (and (inv x y ) (< x 0)) (= x1 (+ x y))) (= y1 (+ y 1)))) (inv x1 y1 )))
(constraint (or (not (and (inv x y ) (>= x 0))) (> y 0)))
(check-synth)


