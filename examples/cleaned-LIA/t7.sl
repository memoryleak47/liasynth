; printing sygus problem  

(set-logic LIA)
(declare-var bufferIndex_125-10-125-47 Int)

(declare-var MC_741360_125-10-125-47 Int)

(synth-fun f_125-10-125-47((bufferIndex Int)(MC_741360 Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (bufferIndex MC_741360 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (=> (and (= bufferIndex_125-10-125-47 1) (= MC_741360_125-10-125-47 0)) (= (f_125-10-125-47 bufferIndex_125-10-125-47 MC_741360_125-10-125-47 ) false)))
(check-synth)


