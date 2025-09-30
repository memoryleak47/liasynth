; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var d Int)

(declare-var s Int)

(declare-var x1 Int)

(declare-var d1 Int)

(declare-var d2 Int)

(declare-var c1 Bool)

(declare-var c2 Bool)

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

(synth-fun __SYNTHFUN_inv((x Int)(d Int)) Bool
((Start Bool)(AtomicFormula Bool)(Sum Int)(Term Int)(Sign Int)(Var Int)(Const Int))
((Start Bool ((and AtomicFormula AtomicFormula) (or AtomicFormula AtomicFormula) ))
(AtomicFormula Bool ((<= Sum Const) (= Sum Const) ))
(Sum Int ((+ Term Term) ))
(Term Int ((* Sign Var) ))
(Sign Int (0 1 (- 1) ))
(Var Int (x d ))
(Const Int ((- 3) (- 2) (- 1) 0 1 2 3 ))
)
)

(constraint (=> (and5 (= d 1) (=> c1 (= d1 (- d 1))) (=> (not c1) (= d1 d)) (=> c2 (= d2 (- d1 1))) (=> (not c2) (= d2 d1)) ) (__SYNTHFUN_inv x d2 )))
(constraint (=> (and3 (__SYNTHFUN_inv x d ) (> x 0) (= x1 (- x d)) ) (__SYNTHFUN_inv x1 d )))
(constraint (=> (and (__SYNTHFUN_inv x d ) (<= x 0)) (<= x 0)))
(check-synth)


