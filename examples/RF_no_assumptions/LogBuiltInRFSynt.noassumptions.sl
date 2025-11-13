; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var inI0 Int)

(declare-var x!15 Int)

(declare-var x!M4 Int)

(declare-var res!M4 Int)

(declare-var res!18 Int)

(declare-var J9 Bool)

(declare-var resPostExec Int)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (= J9 (<= x!M4 1)) (= x!15 (/ x!M4 2))) (= res!18 (+ 1 res!M4))) (=> (not J9) (= xPostExec x!15))) (=> (not J9) (= resPostExec res!18))) (not J9)) (= inI0 0)) (>= res!M4 0)) (and (> (rankingFunction!0 x!M4 res!M4 ) (rankingFunction!0 xPostExec resPostExec )) (>= (rankingFunction!0 x!M4 res!M4 ) 0))))
(check-synth)


