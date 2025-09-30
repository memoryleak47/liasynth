; printing sygus problem  

(set-logic LIA)
(declare-var charno_97-11-98-60 Int)

(declare-var MC_505948_97-11-98-60 Int)

(declare-var MC_741360_97-11-98-60 Bool)

(synth-fun __SYNTHFUN_f_97-11-98-60((charno Int)(MC_505948 Int)(MC_741360 Bool)) Bool
((Start Bool)(IntExpr Int))
((Start Bool ((< IntExpr IntExpr) (<= IntExpr IntExpr) (and Start Start) (> IntExpr IntExpr) (>= IntExpr IntExpr) MC_741360 ))
(IntExpr Int (charno MC_505948 0 1 ))
)
)

(constraint (=> (and (= MC_505948_97-11-98-60 7) (and (= MC_741360_97-11-98-60 true) (= charno_97-11-98-60 7))) (= (__SYNTHFUN_f_97-11-98-60 charno_97-11-98-60 MC_505948_97-11-98-60 MC_741360_97-11-98-60 ) true)))
(constraint (=> (and (= MC_505948_97-11-98-60 10) (and (= MC_741360_97-11-98-60 true) (= charno_97-11-98-60 10))) (= (__SYNTHFUN_f_97-11-98-60 charno_97-11-98-60 MC_505948_97-11-98-60 MC_741360_97-11-98-60 ) true)))
(check-synth)


