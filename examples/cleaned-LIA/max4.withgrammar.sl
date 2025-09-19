; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(declare-var w Int)

(synth-fun max4((x Int)(y Int)(z Int)(w Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x y z w 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (>= (max4 x y z w ) x))
(constraint (>= (max4 x y z w ) y))
(constraint (>= (max4 x y z w ) z))
(constraint (>= (max4 x y z w ) w))
(constraint (or (= x (max4 x y z w )) (or (= y (max4 x y z w )) (or (= z (max4 x y z w )) (= w (max4 x y z w ))))))
(check-synth)


