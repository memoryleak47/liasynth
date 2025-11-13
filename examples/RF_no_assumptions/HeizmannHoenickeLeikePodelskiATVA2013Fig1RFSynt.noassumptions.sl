; printing sygus problem  

(set-logic LIA)
(declare-var xPostExec Int)

(declare-var inI0 Int)

(declare-var x!14 Int)

(declare-var y!M4 Int)

(declare-var x!M4 Int)

(declare-var J8 Bool)

(declare-var yPostExec Int)

(declare-var y!20 Int)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (= J8 (not (<= 0 x!M4))) (= x!14 (+ x!M4 (* (- 1) y!M4)))) (= y!20 (+ 1 y!M4))) (=> (not J8) (= xPostExec x!14))) (=> (not J8) (= yPostExec y!20))) (not J8)) (= inI0 23)) (> y!M4 0)) (>= y!M4 0)) (and (> (rankingFunction!0 x!M4 y!M4 ) (rankingFunction!0 xPostExec yPostExec )) (>= (rankingFunction!0 x!M4 y!M4 ) 0))))
(check-synth)


