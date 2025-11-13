; printing sygus problem  

(set-logic LIA)
(declare-var inI3 Int)

(declare-var inB2 Bool)

(declare-var z!M0 Int)

(declare-var inI0 Int)

(declare-var z!17 Int)

(declare-var zPostExec Int)

(declare-var qPostExec Int)

(declare-var q!12 Int)

(declare-var q!M0 Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (= J4 (<= q!M0 0)) (= q!12 (+ (- 1) q!M0 z!M0))) (= z!17 (* (- 1) z!M0))) (=> (not J4) (= qPostExec q!12))) (=> (not J4) (= zPostExec z!17))) (not J4)) (= inB2 (<= inI3 0))) (= q!M0 (+ (- 1) inI3 inI0))) (= z!M0 (* (- 1) inI0))) (not inB2)) (and (> (rankingFunction!0 q!M0 z!M0 ) (rankingFunction!0 qPostExec zPostExec )) (>= (rankingFunction!0 q!M0 z!M0 ) 0))))
(check-synth)


