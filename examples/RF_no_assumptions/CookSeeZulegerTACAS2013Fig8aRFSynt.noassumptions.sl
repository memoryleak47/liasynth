; printing sygus problem  

(set-logic LIA)
(declare-var x!22 Int)

(declare-var xPostExec Int)

(declare-var x!M0 Int)

(declare-var x!14 Int)

(declare-var J8 Bool)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (= J4 (= x!M0 0)) (= J8 (<= x!M0 0))) (= x!22 (+ 1 x!M0))) (= x!14 (+ (- 1) x!M0))) (=> (and (not J4) J8) (= xPostExec x!22))) (=> (and (not J4) (not J8)) (= xPostExec x!14))) (or (and (not J4) J8) (and (not J4) (not J8)))) (and (> (rankingFunction!0 x!M0 ) (rankingFunction!0 xPostExec )) (>= (rankingFunction!0 x!M0 ) 0))))
(check-synth)


