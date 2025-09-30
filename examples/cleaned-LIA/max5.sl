; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(declare-var w Int)

(declare-var u Int)

(synth-fun max5((x Int)(y Int)(z Int)(w Int)(u Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y z w u 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (>= (max5 x y z w u ) x))
(constraint (>= (max5 x y z w u ) y))
(constraint (>= (max5 x y z w u ) z))
(constraint (>= (max5 x y z w u ) w))
(constraint (>= (max5 x y z w u ) u))
(constraint (or (= x (max5 x y z w u )) (or (= y (max5 x y z w u )) (or (= z (max5 x y z w u )) (or (= w (max5 x y z w u )) (= u (max5 x y z w u )))))))
(check-synth)


