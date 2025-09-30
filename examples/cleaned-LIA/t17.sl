; printing sygus problem  

(set-logic LIA)
(declare-var j_255-8-255-24 Int)

(declare-var MC_741360_255-8-255-24 Int)

(synth-fun f_255-8-255-24((j Int)(MC_741360 Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (j MC_741360 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (and (=> (and (= j_255-8-255-24 2) (= MC_741360_255-8-255-24 3)) (= (f_255-8-255-24 j_255-8-255-24 MC_741360_255-8-255-24 ) true)) (=> (and (= MC_741360_255-8-255-24 3) (= j_255-8-255-24 2)) (= (f_255-8-255-24 j_255-8-255-24 MC_741360_255-8-255-24 ) true))))
(check-synth)


