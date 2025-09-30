; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(declare-var x1 Int)

(declare-var y1 Int)

(synth-fun __SYNTHFUN_inv((x Int)(y Int)) Bool
((Start Bool)(AtomicFormula Bool)(Sum Int)(Term Int)(Sign Int)(Var Int)(Const Int))
((Start Bool ((and AtomicFormula AtomicFormula) (or AtomicFormula AtomicFormula) ))
(AtomicFormula Bool ((<= Sum Const) (= Sum Const) ))
(Sum Int ((+ Term Term) ))
(Term Int ((* Sign Var) ))
(Sign Int (0 1 (- 1) ))
(Var Int (x y ))
(Const Int ((+ Const Const) (- Const Const) 0 1 ))
)
)

(constraint (or (not (= 0 (+ x 50))) (__SYNTHFUN_inv x y )))
(constraint (or (not (and (and (and (__SYNTHFUN_inv x y ) (< x 0)) (= x1 (+ x y))) (= y1 (+ y 1)))) (__SYNTHFUN_inv x1 y1 )))
(constraint (or (not (and (__SYNTHFUN_inv x y ) (>= x 0))) (> y 0)))
(check-synth)


