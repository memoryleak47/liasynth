; printing sygus problem  

(set-logic LIA)
(declare-var x1 Int)

(declare-var x2 Int)

(declare-var k Int)

(synth-fun __SYNTHFUN_findIdx((y1 Int)(y2 Int)(k1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (y1 y2 k1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (< x1 x2) (=> (< k x1) (= (__SYNTHFUN_findIdx x1 x2 k ) 0))))
(constraint (=> (< x1 x2) (=> (> k x2) (= (__SYNTHFUN_findIdx x1 x2 k ) 2))))
(constraint (=> (< x1 x2) (=> (and (> k x1) (< k x2)) (= (__SYNTHFUN_findIdx x1 x2 k ) 1))))
(check-synth)


