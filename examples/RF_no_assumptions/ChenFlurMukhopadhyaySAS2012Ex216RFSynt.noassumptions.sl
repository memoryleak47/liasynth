; printing sygus problem  

(set-logic LIA)
(declare-var x!8 Int)

(declare-var xPostExec Int)

(declare-var y!M0 Int)

(declare-var y!14 Int)

(declare-var x!M0 Int)

(declare-var yPostExec Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (= J4 (<= x!M0 0)) (= x!8 y!M0)) (= y!14 (+ (- 1) y!M0))) (=> (not J4) (= xPostExec x!8))) (=> (not J4) (= yPostExec y!14))) (not J4)) (and (> (rankingFunction!0 x!M0 y!M0 ) (rankingFunction!0 xPostExec yPostExec )) (>= (rankingFunction!0 x!M0 y!M0 ) 0))))
(check-synth)


