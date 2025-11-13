; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var x!10 Int)

(declare-var y!M0 Int)

(declare-var x!M0 Int)

(declare-var J14 Bool)

(declare-var yPostExec Int)

(declare-var y!20 Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (= J4 (not (<= 0 x!M0))) (= x!10 (+ x!M0 y!M0))) (= J14 (not (<= 0 y!M0)))) (= y!20 (+ (- 1) y!M0))) (=> (and (not J4) J14) (= xPostExec x!10))) (=> (and (not J4) J14) (= yPostExec y!M0))) (=> (and (not J4) (not J14)) (= xPostExec x!10))) (=> (and (not J4) (not J14)) (= yPostExec y!20))) (or (and (not J4) J14) (and (not J4) (not J14)))) (and (> (rankingFunction!0 x!M0 y!M0 ) (rankingFunction!0 xPostExec yPostExec )) (>= (rankingFunction!0 x!M0 y!M0 ) 0))))
(check-synth)


