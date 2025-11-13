; printing sygus problem  

(set-logic LIA)
(declare-var x!22 Int)

(declare-var xPostExec Int)

(declare-var inB3 Bool)

(declare-var inB0 Bool)

(declare-var y!M6 Int)

(declare-var x!M6 Int)

(declare-var J16 Bool)

(declare-var y!30 Int)

(declare-var J11 Bool)

(declare-var yPostExec Int)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= J11 (= x!M6 y!M6)) (= J16 (<= x!M6 y!M6))) (= y!30 (+ y!M6 (* (- 1) x!M6)))) (= x!22 (+ x!M6 (* (- 1) y!M6)))) (=> (and (not J11) J16) (= xPostExec x!M6))) (=> (and (not J11) J16) (= yPostExec y!30))) (=> (and (not J11) (not J16)) (= xPostExec x!22))) (=> (and (not J11) (not J16)) (= yPostExec y!M6))) (or (and (not J11) J16) (and (not J11) (not J16)))) (= inB0 (<= x!M6 0))) (= inB3 (<= y!M6 0))) (and (not inB0) (not inB3))) (> x!M6 0)) (> y!M6 0)) (>= x!M6 0)) (>= y!M6 0)) (and (> (rankingFunction!0 x!M6 y!M6 ) (rankingFunction!0 xPostExec yPostExec )) (>= (rankingFunction!0 x!M6 y!M6 ) 0))))
(check-synth)


