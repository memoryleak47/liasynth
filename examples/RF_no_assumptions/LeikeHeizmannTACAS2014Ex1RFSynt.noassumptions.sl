; printing sygus problem  

(set-logic LIA)
(declare-var y!0 Int)

(declare-var q!16 Int)

(declare-var q!26 Int)

(declare-var qPostExec Int)

(declare-var J8 Bool)

(declare-var q!M0 Int)

(declare-var yPostExec Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (= J4 (<= q!M0 0)) (= J8 (<= y!0 0))) (= q!26 (+ (- 1) q!M0 y!0))) (= q!16 (+ (- 1) q!M0 (* (- 1) y!0)))) (=> (and (not J4) J8) (= qPostExec q!26))) (=> (and (not J4) (not J8)) (= qPostExec q!16))) (or (and (not J4) J8) (and (not J4) (not J8)))) (= y!0 yPostExec)) (and (> (rankingFunction!0 q!M0 y!0 ) (rankingFunction!0 qPostExec yPostExec )) (>= (rankingFunction!0 q!M0 y!0 ) 0))))
(check-synth)


