; printing sygus problem  

(set-logic LIA)
(declare-var x2_143-17-143-55 Int)

(declare-var x1_143-17-143-55 Int)

(declare-var parentNode_143-17-143-55 Int)

(declare-var EMPTY_PARENT_143-17-143-55 Int)

(synth-fun __SYNTHFUN_f_143-17-143-55((x2 Int)(x1 Int)(parentNode Int)(EMPTY_PARENT Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (x2 x1 parentNode EMPTY_PARENT 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (=> (and (= parentNode_143-17-143-55 0) (and (= EMPTY_PARENT_143-17-143-55 (- 1)) (and (= x2_143-17-143-55 1) (= x1_143-17-143-55 1)))) (= (__SYNTHFUN_f_143-17-143-55 x2_143-17-143-55 x1_143-17-143-55 parentNode_143-17-143-55 EMPTY_PARENT_143-17-143-55 ) true)))
(check-synth)


