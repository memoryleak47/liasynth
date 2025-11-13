; printing sygus problem  

(set-logic LIA)
(declare-var a!35 Int)

(declare-var J28 Bool)

(declare-var B3 Bool)

(declare-var mPostExec Int)

(declare-var J19 Bool)

(declare-var a!M8 Int)

(declare-var b!M8 Int)

(declare-var nPostExec Int)

(declare-var n!0 Int)

(declare-var inI1 Int)

(declare-var m!0 Int)

(declare-var inI0 Int)

(declare-var bPostExec Int)

(declare-var aPostExec Int)

(declare-var b!41 Int)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)(arg3 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 arg3 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= J19 (<= (* (+ 1 a!M8) (+ 1 a!M8)) n!0)) (let ((a!1 (not (<= (* (+ 1 b!M8) (+ 1 b!M8)) m!0)))) (= J28 a!1))) (= B3 (or J19 (and (not J19) (not J28))))) (= a!35 (+ 1 a!M8))) (= b!41 (+ 1 b!M8))) (=> B3 (= aPostExec a!35))) (=> B3 (= bPostExec b!41))) B3) (= inI1 0)) (= inI0 0)) (>= a!M8 0)) (>= b!M8 0)) (= n!0 nPostExec)) (= m!0 mPostExec)) (and (> (rankingFunction!0 n!0 m!0 a!M8 b!M8 ) (rankingFunction!0 nPostExec mPostExec aPostExec bPostExec )) (>= (rankingFunction!0 n!0 m!0 a!M8 b!M8 ) 0))))
(check-synth)


