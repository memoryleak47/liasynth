; SMTLIB-v2 
; result is unsat 
(set-logic LIA)
(define-fun f ((x Int) (y Int)) Int 
(ite (= x y) 0
(ite (> x y) 1
(- 1))))


(declare-fun x  () Int)
(declare-fun y  () Int)
(assert (or (not (or (and (= x y) (= (f x y) 0)) (or (and (> x y) (= (f x y) 1)) (= (f x y) (- 1)))))))
(check-sat)
