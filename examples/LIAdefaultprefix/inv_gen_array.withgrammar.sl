; printing sygus problem  

(set-logic LIA)
(declare-var m Int)

(declare-var j Int)

(declare-var a0 Int)

(declare-var s Int)

(declare-var t Int)

(declare-var a1 Int)

(declare-var a2 Int)

(declare-var a3 Int)

(declare-var a4 Int)

(declare-var j1 Int)

(declare-var m1 Int)

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

(synth-fun __SYNTHFUN_inv((m Int)(j Int)(a0 Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (m j a0 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (=> (and (= s 5) (= 0 j)) (__SYNTHFUN_inv m j a0 )))
(constraint (=> (and6 (= j 0) (__SYNTHFUN_inv m j a0 ) (< j s) (= a0 t) (or (and (<= a0 m) (= m1 a0)) (and (> a0 m) (= m1 m))) (= j1 (+ j 1)) ) (__SYNTHFUN_inv m1 j1 a0 )))
(constraint (=> (and6 (= j 1) (__SYNTHFUN_inv m j a0 ) (< j s) (= a1 t) (or (and (<= a1 m) (= m1 a1)) (and (> a1 m) (= m1 m))) (= j1 (+ j 1)) ) (__SYNTHFUN_inv m1 j1 a0 )))
(constraint (=> (and6 (= j 2) (__SYNTHFUN_inv m j a0 ) (< j s) (= a2 t) (or (and (<= a2 m) (= m1 a2)) (and (> a2 m) (= m1 m))) (= j1 (+ j 1)) ) (__SYNTHFUN_inv m1 j1 a0 )))
(constraint (=> (and6 (= j 3) (__SYNTHFUN_inv m j a0 ) (< j s) (= a3 t) (or (and (<= a3 m) (= m1 a3)) (and (> a3 m) (= m1 m))) (= j1 (+ j 1)) ) (__SYNTHFUN_inv m1 j1 a0 )))
(constraint (=> (and6 (= j 4) (__SYNTHFUN_inv m j a0 ) (< j s) (= a4 t) (or (and (<= a4 m) (= m1 a4)) (and (> a4 m) (= m1 m))) (= j1 (+ j 1)) ) (__SYNTHFUN_inv m1 j1 a0 )))
(constraint (=> (and3 (= j 5) (__SYNTHFUN_inv m j a0 ) (>= j s) ) (>= a0 m)))
(check-synth)


