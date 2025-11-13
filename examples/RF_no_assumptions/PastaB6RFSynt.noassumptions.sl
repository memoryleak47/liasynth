; printing sygus problem  

(set-logic LIA)
(declare-var y!12 Int)

(declare-var inI3 Int)

(declare-var xPostExec Int)

(declare-var y!M0 Int)

(declare-var inI1 Int)

(declare-var inB4 Bool)

(declare-var x!M0 Int)

(declare-var J6 Bool)

(declare-var inB5 Bool)

(declare-var yPostExec Int)

(declare-var x!9 Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= J4 (<= x!M0 0)) (= J6 (<= y!M0 0))) (= x!9 (+ (- 1) x!M0))) (= y!12 (+ (- 1) y!M0))) (=> (and (not J4) (not J6)) (= xPostExec x!9))) (=> (and (not J4) (not J6)) (= yPostExec y!12))) (and (not J4) (not J6))) (= inB4 (<= inI3 0))) (= inB5 (<= inI1 0))) (= x!M0 (+ (- 1) inI3))) (= y!M0 (+ (- 1) inI1))) (and (not inB4) (not inB5))) (>= x!M0 0)) (>= y!M0 0)) (and (> (rankingFunction!0 x!M0 y!M0 ) (rankingFunction!0 xPostExec yPostExec )) (>= (rankingFunction!0 x!M0 y!M0 ) 0))))
(check-synth)


