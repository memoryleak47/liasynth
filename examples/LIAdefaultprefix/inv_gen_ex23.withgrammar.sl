; printing sygus problem  

(set-logic LIA)
(declare-var y Int)

(declare-var z Int)

(declare-var c Int)

(declare-var y1 Int)

(declare-var z1 Int)

(declare-var c1 Int)

(define-fun implies ((b1 Bool)(b2 Bool)) Bool
 (or (not b1) b2))

(define-fun and3 ((b1 Bool)(b2 Bool)(b3 Bool)) Bool
 (and (and b1 b2) b3))

(define-fun or3 ((b1 Bool)(b2 Bool)(b3 Bool)) Bool
 (or (or b1 b2) b3))

(define-fun and4 ((b1 Bool)(b2 Bool)(b3 Bool)(b4 Bool)) Bool
 (and (and3 b1 b2 b3 ) b4))

(define-fun or4 ((b1 Bool)(b2 Bool)(b3 Bool)(b4 Bool)) Bool
 (or (or3 b1 b2 b3 ) b4))

(define-fun and5 ((b1 Bool)(b2 Bool)(b3 Bool)(b4 Bool)(b5 Bool)) Bool
 (and (and4 b1 b2 b3 b4 ) b5))

(define-fun or5 ((b1 Bool)(b2 Bool)(b3 Bool)(b4 Bool)(b5 Bool)) Bool
 (or (or4 b1 b2 b3 b4 ) b5))

(define-fun and6 ((b1 Bool)(b2 Bool)(b3 Bool)(b4 Bool)(b5 Bool)(b6 Bool)) Bool
 (and (and5 b1 b2 b3 b4 b5 ) b6))

(synth-fun __SYNTHFUN_inv((y Int)(z Int)(c Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (y z c 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (=> (and (= c 0) (< 127 y)) true))
(constraint (=> (and3 (= c 0) (>= 127 y) (< y 0) ) true))
(constraint (=> (and4 (= c 0) (>= 127 y) (>= y 0) (= z (* y 36)) ) (__SYNTHFUN_inv y z c )))
(constraint (=> (and5 (__SYNTHFUN_inv y z c ) (< c 36) (not (or (< z 0) (>= z 4608))) (= z1 (+ z 1)) (= c1 (+ c 1)) ) (__SYNTHFUN_inv y z1 c1 )))
(constraint (=> (and3 (__SYNTHFUN_inv y z c ) (< c 36) (or (< z 0) (>= z 4608)) ) false))
(check-synth)


