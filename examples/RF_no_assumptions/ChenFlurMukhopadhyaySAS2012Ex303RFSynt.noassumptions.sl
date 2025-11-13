; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var zPostExec Int)

(declare-var yPostExec Int)

(declare-var inI3 Int)

(declare-var inI2 Int)

(declare-var x!10 Int)

(declare-var y!M0 Int)

(declare-var inI1 Int)

(declare-var z!M0 Int)

(declare-var inB4 Bool)

(declare-var y!16 Int)

(declare-var x!M0 Int)

(declare-var z!22 Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (= J4 (<= x!M0 0)) (= x!10 (+ x!M0 y!M0))) (= y!16 (+ y!M0 z!M0))) (= z!22 (+ (- 1) z!M0))) (=> (not J4) (= xPostExec x!10))) (=> (not J4) (= yPostExec y!16))) (=> (not J4) (= zPostExec z!22))) (not J4)) (= inB4 (<= inI3 0))) (= x!M0 (+ inI3 inI1))) (= y!M0 (+ inI1 inI2))) (= z!M0 (+ (- 1) inI2))) (not inB4)) (and (> (rankingFunction!0 x!M0 y!M0 z!M0 ) (rankingFunction!0 xPostExec yPostExec zPostExec )) (>= (rankingFunction!0 x!M0 y!M0 z!M0 ) 0))))
(check-synth)


