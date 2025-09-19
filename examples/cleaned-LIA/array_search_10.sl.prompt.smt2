; SMTLIB-v2 
; result is unsat 
(set-logic LIA)
(declare-fun x1  () Int)
(declare-fun x2  () Int)
(declare-fun x3  () Int)
(declare-fun x4  () Int)
(declare-fun x5  () Int)
(declare-fun x6  () Int)
(declare-fun x7  () Int)
(declare-fun x8  () Int)
(declare-fun x9  () Int)
(declare-fun x10  () Int)
(declare-fun k  () Int)
(assert (or (not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (< k x1) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 0))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (> k x10) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 10))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x1) (< k x2)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 1))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x2) (< k x3)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 2))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x3) (< k x4)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 3))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x4) (< k x5)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 4))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x5) (< k x6)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 5))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x6) (< k x7)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 6))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x7) (< k x8)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 7))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x8) (< k x9)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 8))))(not (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (< x9 x10))))))))) (=> (and (> k x9) (< k x10)) (= (f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k) 9))))))
(check-sat)
; define function f
(define-fun f ((y1 Int) (y2 Int) (y3 Int) (y4 Int) (y5 Int) (y6 Int) (y7 Int) (y8 Int) (y9 Int) (y10 Int) (k1 Int)) Int
(