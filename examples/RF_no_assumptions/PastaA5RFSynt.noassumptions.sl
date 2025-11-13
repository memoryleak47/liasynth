; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var y!M0 Int)

(declare-var inB3 Bool)

(declare-var inI1 Int)

(declare-var x!0 Int)

(declare-var J7 Bool)

(declare-var y!10 Int)

(declare-var yPostExec Int)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (= J7 (not (<= y!M0 (+ (- 1) x!0)))) (= y!10 (+ 1 y!M0))) (=> (not J7) (= yPostExec y!10))) (not J7)) (= inB3 (not (<= inI1 (+ (- 1) x!0))))) (= y!M0 (+ 1 inI1))) (not inB3)) (= x!0 xPostExec)) (and (> (rankingFunction!0 x!0 y!M0 ) (rankingFunction!0 xPostExec yPostExec )) (>= (rankingFunction!0 x!0 y!M0 ) 0))))
(check-synth)


