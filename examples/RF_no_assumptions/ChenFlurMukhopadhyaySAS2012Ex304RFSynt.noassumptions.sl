; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var z!0 Int)

(declare-var zPostExec Int)

(declare-var yPostExec Int)

(declare-var y!23 Int)

(declare-var inI3 Int)

(declare-var inB2 Bool)

(declare-var y!M0 Int)

(declare-var inI1 Int)

(declare-var x!M0 Int)

(declare-var x!17 Int)

(declare-var J6 Bool)

(declare-var J9 Bool)

(declare-var inB5 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (= J6 (not (<= 0 (+ x!M0 y!M0)))) (= J9 (not (<= x!M0 z!0)))) (= x!17 (+ (* 2 x!M0) y!M0))) (= y!23 (+ 1 y!M0))) (=> (and (not J6) (not J9)) (= xPostExec x!17))) (=> (and (not J6) (not J9)) (= yPostExec y!23))) (and (not J6) (not J9))) (= inB5 (not (<= 0 (+ inI3 inI1))))) (= inB2 (not (<= inI3 z!0)))) (= x!M0 (+ (* 2 inI3) inI1))) (= y!M0 (+ 1 inI1))) (and (not inB5) (not inB2))) (= z!0 zPostExec)) (and (> (rankingFunction!0 x!M0 y!M0 z!0 ) (rankingFunction!0 xPostExec yPostExec zPostExec )) (>= (rankingFunction!0 x!M0 y!M0 z!0 ) 0))))
(check-synth)


