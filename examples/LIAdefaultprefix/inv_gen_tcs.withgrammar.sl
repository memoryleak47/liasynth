; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var i Int)

(declare-var j Int)

(declare-var s Int)

(declare-var x1 Int)

(declare-var y1 Int)

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

(synth-fun __SYNTHFUN_inv((x Int)(y Int)(i Int)(j Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (x y i j 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (=> (and (= x i) (= y j)) (__SYNTHFUN_inv x y i j )))
(constraint (=> (and4 (__SYNTHFUN_inv x y i j ) (not (= x 0)) (= x1 (- x 1)) (= y1 (- y 1)) ) (__SYNTHFUN_inv x1 y1 i j )))
(constraint (=> (and3 (__SYNTHFUN_inv x y i j ) (= x 0) (= i j) ) (= y 0)))
(check-synth)


