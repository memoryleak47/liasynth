; printing sygus problem  

(set-logic LIA)
(declare-var a!M0 Int)

(declare-var b!M0 Int)

(declare-var b!28 Int)

(declare-var bPostExec Int)

(declare-var J14 Bool)

(declare-var aPostExec Int)

(declare-var a!10 Int)

(declare-var b!21 Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (= J4 (not (<= 0 a!M0))) (= a!10 (+ a!M0 b!M0))) (= J14 (not (<= 0 b!M0)))) (= b!28 (* (- 1) b!M0))) (= b!21 (+ (- 1) (* (- 1) b!M0)))) (=> (and (not J4) J14) (= aPostExec a!10))) (=> (and (not J4) J14) (= bPostExec b!28))) (=> (and (not J4) (not J14)) (= aPostExec a!10))) (=> (and (not J4) (not J14)) (= bPostExec b!21))) (or (and (not J4) J14) (and (not J4) (not J14)))) (and (> (rankingFunction!0 a!M0 b!M0 ) (rankingFunction!0 aPostExec bPostExec )) (>= (rankingFunction!0 a!M0 b!M0 ) 0))))
(check-synth)


