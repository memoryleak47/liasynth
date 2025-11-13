; printing sygus problem  

(set-logic LIA)
(declare-var B3 Bool)

(declare-var mPostExec Int)

(declare-var a!27 Int)

(declare-var a!M8 Int)

(declare-var b!M8 Int)

(declare-var nPostExec Int)

(declare-var n!0 Int)

(declare-var inI1 Int)

(declare-var m!0 Int)

(declare-var inI0 Int)

(declare-var bPostExec Int)

(declare-var J15 Bool)

(declare-var aPostExec Int)

(declare-var J20 Bool)

(declare-var b!33 Int)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)(arg3 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 arg3 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (= J15 (<= (* a!M8 a!M8) n!0)) (= J20 (not (<= (* b!M8 b!M8) m!0)))) (= B3 (or J15 (and (not J15) (not J20))))) (= a!27 (+ 1 a!M8))) (= b!33 (+ 1 b!M8))) (=> B3 (= aPostExec a!27))) (=> B3 (= bPostExec b!33))) B3) (= inI1 0)) (= inI0 0)) (>= a!M8 0)) (>= b!M8 0)) (= n!0 nPostExec)) (= m!0 mPostExec)) (and (> (rankingFunction!0 n!0 m!0 a!M8 b!M8 ) (rankingFunction!0 nPostExec mPostExec aPostExec bPostExec )) (>= (rankingFunction!0 n!0 m!0 a!M8 b!M8 ) 0))))
(check-synth)


