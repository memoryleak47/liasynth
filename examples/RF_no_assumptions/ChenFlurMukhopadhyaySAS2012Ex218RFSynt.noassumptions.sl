; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var inI2 Int)

(declare-var y!M0 Int)

(declare-var inB3 Bool)

(declare-var inI1 Int)

(declare-var x!12 Int)

(declare-var x!M0 Int)

(declare-var y!18 Int)

(declare-var yPostExec Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (= J4 (<= x!M0 0)) (= x!12 (+ (- 5) x!M0 y!M0))) (= y!18 (* (- 2) y!M0))) (=> (not J4) (= xPostExec x!12))) (=> (not J4) (= yPostExec y!18))) (not J4)) (= inB3 (<= inI2 0))) (= x!M0 (+ (- 5) inI2 inI1))) (= y!M0 (* (- 2) inI1))) (not inB3)) (and (> (rankingFunction!0 x!M0 y!M0 ) (rankingFunction!0 xPostExec yPostExec )) (>= (rankingFunction!0 x!M0 y!M0 ) 0))))
(check-synth)


