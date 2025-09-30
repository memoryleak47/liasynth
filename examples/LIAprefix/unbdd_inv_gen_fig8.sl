; printing sygus problem  

(set-logic LIA)
(declare-var l Int)

(declare-var x0 Int)

(declare-var x1 Int)

(declare-var x2 Int)

(declare-var x3 Int)

(declare-var x4 Int)

(declare-var x0p Int)

(declare-var x1p Int)

(declare-var x2p Int)

(declare-var x3p Int)

(declare-var x4p Int)

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

(synth-fun __SYNTHFUN_inv((l Int)) Bool
((Start Bool)(AtomicFormula Bool)(Sum Int)(Term Int)(Sign Int)(Var Int)(Const Int))
((Start Bool ((and AtomicFormula AtomicFormula) (or AtomicFormula AtomicFormula) ))
(AtomicFormula Bool ((<= Sum Const) (= Sum Const) ))
(Sum Int ((+ Term Term) ))
(Term Int ((* Sign Var) ))
(Sign Int (0 1 (- 1) ))
(Var Int (l ))
(Const Int ((+ Const Const) (- Const Const) 0 1 ))
)
)

(constraint (=> (and6 (= l 0) (or (= x0p (+ x0 1)) (= x0p (- x0 1))) (or (= x1p (+ x1 1)) (= x1p (- x1 1))) (or (= x2p (+ x2 1)) (= x2p (- x2 1))) (or (= x3p (+ x3 1)) (= x3p (- x3 1))) (or (= x4p (+ x4 1)) (= x4p (- x4 1))) ) (__SYNTHFUN_inv l )))
(constraint (=> (and (__SYNTHFUN_inv l ) (not (= l 0))) false))
(check-synth)


