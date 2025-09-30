; printing sygus problem  

(set-logic LIA)
(declare-var x2_143-17-143-55 Int)

(declare-var x1_143-17-143-55 Int)

(declare-var parentNode_143-17-143-55 Int)

(declare-var EMPTY_PARENT_143-17-143-55 Int)

(synth-fun __SYNTHFUN_f_143-17-143-55((x2 Int)(x1 Int)(parentNode Int)(EMPTY_PARENT Int)) Bool
((Start Bool)(IntExpr Int))
((Start Bool ((< IntExpr IntExpr) (and Start Start) (= IntExpr IntExpr) (not Start) (<= IntExpr IntExpr) (or Start Start) ))
(IntExpr Int (x2 x1 parentNode EMPTY_PARENT 0 1 ))
)
)

(constraint (=> (and (= parentNode_143-17-143-55 0) (and (= EMPTY_PARENT_143-17-143-55 (- 1)) (and (= x2_143-17-143-55 1) (= x1_143-17-143-55 1)))) (= (__SYNTHFUN_f_143-17-143-55 x2_143-17-143-55 x1_143-17-143-55 parentNode_143-17-143-55 EMPTY_PARENT_143-17-143-55 ) true)))
(check-synth)


