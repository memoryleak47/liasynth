; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var x!0 Int)

(declare-var zPostExec Int)

(declare-var inI5 Int)

(declare-var yPostExec Int)

(declare-var y!11 Int)

(declare-var inI2 Int)

(declare-var y!M0 Int)

(declare-var z!M0 Int)

(declare-var inB4 Bool)

(declare-var z!14 Int)

(declare-var J8 Bool)

(declare-var inB6 Bool)

(declare-var J5 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (= J5 (<= x!0 y!M0)) (= J8 (<= x!0 z!M0))) (= y!11 (+ 1 y!M0))) (= z!14 (+ 1 z!M0))) (=> (and (not J5) (not J8)) (= yPostExec y!11))) (=> (and (not J5) (not J8)) (= zPostExec z!14))) (and (not J5) (not J8))) (= inB6 (<= x!0 inI2))) (= inB4 (<= x!0 inI5))) (= y!M0 (+ 1 inI2))) (= z!M0 (+ 1 inI5))) (and (not inB6) (not inB4))) (= x!0 xPostExec)) (and (> (rankingFunction!0 x!0 y!M0 z!M0 ) (rankingFunction!0 xPostExec yPostExec zPostExec )) (>= (rankingFunction!0 x!0 y!M0 z!M0 ) 0))))
(check-synth)


