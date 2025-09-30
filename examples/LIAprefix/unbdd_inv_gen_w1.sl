; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var n Int)

(declare-var s Int)

(declare-var x1 Int)

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

(synth-fun __SYNTHFUN_inv((x Int)(n Int)) Bool
((Start Bool)(AtomicFormula Bool)(Sum Int)(Term Int)(Sign Int)(Var Int)(Const Int))
((Start Bool ((and AtomicFormula AtomicFormula) (or AtomicFormula AtomicFormula) ))
(AtomicFormula Bool ((<= Sum Const) (= Sum Const) ))
(Sum Int ((+ Term Term) ))
(Term Int ((* Sign Var) ))
(Sign Int (0 1 (- 1) ))
(Var Int (x n ))
(Const Int ((+ Const Const) (- Const Const) 0 1 ))
)
)

(constraint (=> (and (= x 0) (>= n 0)) (__SYNTHFUN_inv x n )))
(constraint (=> (and3 (__SYNTHFUN_inv x n ) (< x n) (= x1 (+ x 1)) ) (__SYNTHFUN_inv x1 n )))
(constraint (=> (and (__SYNTHFUN_inv x n ) (>= x n)) (= x n)))
(check-synth)


