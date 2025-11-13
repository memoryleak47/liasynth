; printing sygus problem  

(set-logic LIA)
(declare-var a!M0 Int)

(declare-var b!M0 Int)

(declare-var tmp!10 Int)

(declare-var tmp!M0 Int)

(declare-var b!16 Int)

(declare-var bPostExec Int)

(declare-var J6 Bool)

(declare-var aPostExec Int)

(declare-var a!20 Int)

(declare-var tmpPostExec Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= J4 (<= b!M0 0)) (= J6 (<= a!M0 0))) (= tmp!10 b!M0)) (= b!16 (mod a!M0 b!M0))) (= a!20 tmp!10)) (=> (and (not J4) (not J6)) (= tmpPostExec a!20))) (=> (and (not J4) (not J6)) (= aPostExec b!16))) (=> (and (not J4) (not J6)) (= bPostExec tmp!10))) (and (not J4) (not J6))) (> a!M0 0)) (> tmp!M0 0)) (>= a!M0 0)) (>= b!M0 0)) (>= tmp!M0 0)) (and (> (rankingFunction!0 tmp!M0 a!M0 b!M0 ) (rankingFunction!0 tmpPostExec aPostExec bPostExec )) (>= (rankingFunction!0 tmp!M0 a!M0 b!M0 ) 0))))
(check-synth)


