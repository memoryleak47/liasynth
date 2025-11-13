; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var i!M0 Int)

(declare-var i!11 Int)

(declare-var y!0 Int)

(declare-var zPostExec Int)

(declare-var yPostExec Int)

(declare-var iPostExec Int)

(declare-var x!22 Int)

(declare-var z!M0 Int)

(declare-var x!M0 Int)

(declare-var J16 Bool)

(declare-var z!30 Int)

(declare-var J5 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)(arg3 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 arg3 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (= J5 (>= x!M0 y!0)) (= i!11 (+ 1 i!M0))) (= J16 (<= z!M0 x!M0))) (= z!30 (+ 1 z!M0))) (= x!22 (+ 1 x!M0))) (=> (and (not J5) J16) (= xPostExec x!M0))) (=> (and (not J5) J16) (= zPostExec z!30))) (=> (and (not J5) J16) (= iPostExec i!11))) (=> (and (not J5) (not J16)) (= xPostExec x!22))) (=> (and (not J5) (not J16)) (= zPostExec z!M0))) (=> (and (not J5) (not J16)) (= iPostExec i!11))) (or (and (not J5) J16) (and (not J5) (not J16)))) (= y!0 yPostExec)) (and (> (rankingFunction!0 x!M0 y!0 z!M0 i!M0 ) (rankingFunction!0 xPostExec yPostExec zPostExec iPostExec )) (>= (rankingFunction!0 x!M0 y!0 z!M0 i!M0 ) 0))))
(check-synth)


