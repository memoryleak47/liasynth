; printing sygus problem  

(set-logic LIA)
(declare-var inB1 Bool)

(declare-var y!M0 Int)

(declare-var inI0 Int)

(declare-var y!10 Int)

(declare-var yPostExec Int)

(declare-var J4 Bool)

(synth-fun rankingFunction!0((arg0 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (= J4 (not (<= 0 y!M0))) (= y!10 (+ (- 1) y!M0))) (=> (not J4) (= yPostExec y!10))) (not J4)) (= inB1 (not (<= 0 inI0)))) (= y!M0 (+ (- 1) inI0))) (not inB1)) (and (> (rankingFunction!0 y!M0 ) (rankingFunction!0 yPostExec )) (>= (rankingFunction!0 y!M0 ) 0))))
(check-synth)


