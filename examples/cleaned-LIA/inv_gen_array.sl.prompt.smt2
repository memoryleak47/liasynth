; SMTLIB-v2 
; result is unsat 
(set-logic LIA)
; define function inv
(define-fun inv ((m Int) (j Int) (a0 Int)) Bool
(ite (= j 0) true
(ite (and (>= j 0)(< j 5)) (>= a0 m)
 false ) ))


; (define-fun inv ((m Int) (j Int) (a0 Int)) Bool 
;     (or (<= j 0) (>= a0 m)))


(declare-fun s  () Int)
(declare-fun j  () Int)
(declare-fun t  () Int)
(declare-fun m  () Int)
(declare-fun a0  () Int)
(declare-fun a1  () Int)
(declare-fun a2  () Int)
(declare-fun a3  () Int)
(declare-fun a4  () Int)
(declare-fun j1  () Int)
(declare-fun m1  () Int)
(define-fun implies ((b1 Bool) (b2 Bool)) Bool
    (or (not b1) b2))
(define-fun and3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool
    (and (and b1 b2) b3))
(define-fun and4 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool)) Bool
    (and (and3 b1 b2 b3) b4))
(define-fun and5 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool)) Bool
    (and (and4 b1 b2 b3 b4) b5))
(define-fun and6 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool) (b6 Bool)) Bool
    (and (and5 b1 b2 b3 b4 b5) b6))
(define-fun or3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool
    (or (or b1 b2) b3))
(define-fun or4 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool)) Bool
    (or (or3 b1 b2 b3) b4))
(define-fun or5 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool)) Bool
    (or (or4 b1 b2 b3 b4) b5))
(assert (or (not (implies (and (= s 5) (= 0 j)) (inv m j a0)))(not (implies (and6 (= j 0) (inv m j a0) (< j s) (= a0 t) (or (and (<= a0 m) (= m1 a0)) (and (> a0 m) (= m1 m))) (= j1 (+ j 1))) (inv m1 j1 a0)))(not (implies (and6 (= j 1) (inv m j a0) (< j s) (= a1 t) (or (and (<= a1 m) (= m1 a1)) (and (> a1 m) (= m1 m))) (= j1 (+ j 1))) (inv m1 j1 a0)))(not (implies (and6 (= j 2) (inv m j a0) (< j s) (= a2 t) (or (and (<= a2 m) (= m1 a2)) (and (> a2 m) (= m1 m))) (= j1 (+ j 1))) (inv m1 j1 a0)))(not (implies (and6 (= j 3) (inv m j a0) (< j s) (= a3 t) (or (and (<= a3 m) (= m1 a3)) (and (> a3 m) (= m1 m))) (= j1 (+ j 1))) (inv m1 j1 a0)))(not (implies (and6 (= j 4) (inv m j a0) (< j s) (= a4 t) (or (and (<= a4 m) (= m1 a4)) (and (> a4 m) (= m1 m))) (= j1 (+ j 1))) (inv m1 j1 a0)))(not (implies (and3 (= j 5) (inv m j a0) (>= j s)) (>= a0 m)))))
(check-sat)
(get-model)
