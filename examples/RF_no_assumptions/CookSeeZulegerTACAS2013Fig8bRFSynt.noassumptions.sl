; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var M!0 Int)

(declare-var x!26 Int)

(declare-var inB0 Bool)

(declare-var MPostExec Int)

(declare-var x!M4 Int)

(declare-var x!18 Int)

(declare-var J14 Bool)

(declare-var J9 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (= J9 (= x!M4 M!0)) (= J14 (<= x!M4 M!0))) (= x!26 (+ 1 x!M4))) (= x!18 0)) (=> (and (not J9) J14) (= xPostExec x!26))) (=> (and (not J9) (not J14)) (= xPostExec 0))) (or (and (not J9) J14) (and (not J9) (not J14)))) (= inB0 (<= M!0 0))) (not inB0)) (> M!0 0)) (>= M!0 0)) (= M!0 MPostExec)) (and (> (rankingFunction!0 x!M4 M!0 ) (rankingFunction!0 xPostExec MPostExec )) (>= (rankingFunction!0 x!M4 M!0 ) 0))))
(check-synth)


