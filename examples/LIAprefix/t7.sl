; printing sygus problem  

(set-logic LIA)
(declare-var bufferIndex_125-10-125-47 Int)

(declare-var MC_741360_125-10-125-47 Int)

(synth-fun __SYNTHFUN_f_125-10-125-47((bufferIndex Int)(MC_741360 Int)) Bool
((Start Bool)(IntExpr Int))
((Start Bool ((>= IntExpr IntExpr) (> IntExpr IntExpr) ))
(IntExpr Int ((- IntExpr IntExpr) (+ IntExpr IntExpr) bufferIndex MC_741360 0 1 ))
)
)

(constraint (=> (and (= bufferIndex_125-10-125-47 1) (= MC_741360_125-10-125-47 0)) (= (__SYNTHFUN_f_125-10-125-47 bufferIndex_125-10-125-47 MC_741360_125-10-125-47 ) false)))
(check-synth)


