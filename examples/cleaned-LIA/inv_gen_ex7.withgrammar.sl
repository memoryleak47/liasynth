; printing sygus problem  

(set-logic LIA)
(declare-var i Int)

(declare-var y Int)

(declare-var l Int)

(declare-var x Int)

(declare-var i1 Int)

(declare-var x1 Int)

(declare-var y1 Int)

(declare-var l1 Int)

(synth-fun inv((i Int)(y Int)(l Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (i y l 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

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

(constraint (=> (or3 (< x 0) (< y 0) (> y x) ) true))
(constraint (=> (and3 (not (or3 (< x 0) (< y 0) (> y x) )) (= l x) (= i 0) ) (inv i y l )))
(constraint (=> (and4 (inv i y l ) (< i y) (not (or (< i 0) (>= i l))) (= i1 (+ i 1)) ) (inv i1 y l )))
(constraint (=> (and3 (inv i y l ) (< i y) (or (< i 0) (>= i l)) ) false))
(check-synth)


