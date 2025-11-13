; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var res!25 Int)

(declare-var x!M4 Int)

(declare-var x!18 Int)

(declare-var zPostExec Int)

(declare-var res!M4 Int)

(declare-var yPostExec Int)

(declare-var y!22 Int)

(declare-var z!12 Int)

(declare-var inI0 Int)

(declare-var y!M4 Int)

(declare-var z!M4 Int)

(declare-var J8 Bool)

(declare-var resPostExec Int)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)(arg3 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 arg3 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (= J8 (<= y!M4 0)) (= z!12 x!M4)) (= x!18 (+ (- 1) y!M4))) (= y!22 z!12)) (= res!25 (+ 1 res!M4))) (=> (not J8) (= zPostExec x!18))) (=> (not J8) (= xPostExec y!22))) (=> (not J8) (= yPostExec z!12))) (=> (not J8) (= resPostExec res!25))) (not J8)) (= inI0 0)) (>= res!M4 0)) (and (> (rankingFunction!0 z!M4 x!M4 y!M4 res!M4 ) (rankingFunction!0 zPostExec xPostExec yPostExec resPostExec )) (>= (rankingFunction!0 z!M4 x!M4 y!M4 res!M4 ) 0))))
(check-synth)


