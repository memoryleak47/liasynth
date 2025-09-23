; printing sygus problem  

(set-logic LIA)
(declare-var x1 Int)

(declare-var x2 Int)

(declare-var x3 Int)

(declare-var k Int)

(synth-fun findIdx((y1 Int)(y2 Int)(y3 Int)(k1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (y1 y2 y3 k1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (< x1 x2) (< x2 x3)) (=> (< k x1) (= (findIdx x1 x2 x3 k ) 0))))
(constraint (=> (and (< x1 x2) (< x2 x3)) (=> (> k x3) (= (findIdx x1 x2 x3 k ) 3))))
(constraint (=> (and (< x1 x2) (< x2 x3)) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 x3 k ) 1))))
(constraint (=> (and (< x1 x2) (< x2 x3)) (=> (and (> k x2) (< k x3)) (= (findIdx x1 x2 x3 k ) 2))))
(check-synth)


