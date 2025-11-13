; printing sygus problem  

(set-logic LIA)
(declare-var n!0 Int)

(declare-var m!0 Int)

(declare-var inI0 Int)

(declare-var a!M4 Int)

(declare-var mPostExec Int)

(declare-var a!26 Int)

(declare-var J13 Bool)

(declare-var nPostExec Int)

(declare-var aPostExec Int)

(declare-var J20 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (= J13 (not (<= (* (* 4 a!M4) a!M4) n!0))) (= J20 (not (<= (* (* 4 a!M4) a!M4) m!0)))) (= a!26 (+ 1 a!M4))) (=> (and (not J13) (not J20)) (= aPostExec a!26))) (and (not J13) (not J20))) (= inI0 0)) (>= a!M4 0)) (= n!0 nPostExec)) (= m!0 mPostExec)) (and (> (rankingFunction!0 n!0 m!0 a!M4 ) (rankingFunction!0 nPostExec mPostExec aPostExec )) (>= (rankingFunction!0 n!0 m!0 a!M4 ) 0))))
(check-synth)


