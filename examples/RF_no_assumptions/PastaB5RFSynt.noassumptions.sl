; printing sygus problem  

(set-logic LIA)
(declare-var x!11 Int)

(declare-var xPostExec Int)

(declare-var inB2 Bool)

(declare-var inI1 Int)

(declare-var x!M0 Int)

(declare-var inB0 Bool)

(declare-var J8 Bool)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (= J4 (<= x!M0 0)) (= J8 (not (= (mod x!M0 2) 0)))) (= x!11 (+ (- 1) x!M0))) (=> (and (not J4) (not J8)) (= xPostExec x!11))) (and (not J4) (not J8))) (= inB2 (<= inI1 0))) (= inB0 (not (= (mod inI1 2) 0)))) (= x!M0 (+ (- 1) inI1))) (and (not inB2) (not inB0))) (> x!M0 0)) (>= x!M0 0)) (and (> (rankingFunction!0 x!M0 ) (rankingFunction!0 xPostExec )) (>= (rankingFunction!0 x!M0 ) 0))))
(check-synth)


