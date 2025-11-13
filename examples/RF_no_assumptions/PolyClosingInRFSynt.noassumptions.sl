; printing sygus problem  

(set-logic LIA)
(declare-var n!0 Int)

(declare-var inI0 Int)

(declare-var a!17 Int)

(declare-var a!M4 Int)

(declare-var mPostExec Int)

(declare-var m!M4 Int)

(declare-var m!23 Int)

(declare-var nPostExec Int)

(declare-var aPostExec Int)

(declare-var J11 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (= J11 (not (<= (* a!M4 a!M4) m!M4))) (= a!17 (+ 1 a!M4))) (= m!23 (+ (- 1) m!M4))) (=> (not J11) (= mPostExec m!23))) (=> (not J11) (= aPostExec a!17))) (not J11)) (= inI0 0)) (>= a!M4 0)) (= n!0 nPostExec)) (and (> (rankingFunction!0 n!0 m!M4 a!M4 ) (rankingFunction!0 nPostExec mPostExec aPostExec )) (>= (rankingFunction!0 n!0 m!M4 a!M4 ) 0))))
(check-synth)


