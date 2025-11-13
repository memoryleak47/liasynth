; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var x!10 Int)

(declare-var x!M0 Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (= J4 (<= x!M0 0)) (= x!10 (/ x!M0 2))) (=> (not J4) (= xPostExec x!10))) (not J4)) (>= x!M0 0)) (and (> (rankingFunction!0 x!M0 ) (rankingFunction!0 xPostExec )) (>= (rankingFunction!0 x!M0 ) 0))))
(check-synth)


