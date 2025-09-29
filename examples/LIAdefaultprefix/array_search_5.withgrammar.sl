; printing sygus problem  

(set-logic LIA)
(declare-var x1 Int)

(declare-var x2 Int)

(declare-var x3 Int)

(declare-var x4 Int)

(declare-var x5 Int)

(declare-var k Int)

(synth-fun __SYNTHFUN_findIdx((y1 Int)(y2 Int)(y3 Int)(y4 Int)(y5 Int)(k1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (y1 y2 y3 y4 y5 k1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (< x4 x5)))) (=> (< k x1) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 x5 k ) 0))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (< x4 x5)))) (=> (> k x5) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 x5 k ) 5))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (< x4 x5)))) (=> (and (> k x1) (< k x2)) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 x5 k ) 1))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (< x4 x5)))) (=> (and (> k x2) (< k x3)) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 x5 k ) 2))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (< x4 x5)))) (=> (and (> k x3) (< k x4)) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 x5 k ) 3))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (< x4 x5)))) (=> (and (> k x4) (< k x5)) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 x5 k ) 4))))
(check-synth)


