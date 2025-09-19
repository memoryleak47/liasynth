; SMTLIB-v2 
; result is unsat 
(set-logic LIA)

(define-fun ex ((x Int) (y Int)) Int
(ite (>= x 5) (+ (+ (* 5 x) (* 3 y) 17))
	(+ (* 3 x)1)))

(declare-fun x  () Int)
(declare-fun y  () Int)
(assert (or (not (or (and (>= x 5) (= (ex x y) (+ (* 5 x) (* 3 y) 17))) (and (not (>= x 5)) (= (ex x y) (+ (* 3 x) 1)))))))
(check-sat)
; define function ex
