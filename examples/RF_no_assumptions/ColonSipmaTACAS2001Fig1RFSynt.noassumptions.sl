; printing sygus problem  

(set-logic LIA)
(declare-var tmp!12 Int)

(declare-var i!16 Int)

(declare-var k!28 Int)

(declare-var j!M0 Int)

(declare-var i!M0 Int)

(declare-var tmp!M0 Int)

(declare-var k!M0 Int)

(declare-var j!22 Int)

(declare-var inI7 Int)

(declare-var inI6 Int)

(declare-var tmpPostExec Int)

(declare-var iPostExec Int)

(declare-var inB3 Bool)

(declare-var inI0 Int)

(declare-var J8 Bool)

(declare-var jPostExec Int)

(declare-var J5 Bool)

(declare-var kPostExec Int)

(declare-var inB8 Bool)

(synth-fun rankingFunction!0((arg0 Int)(arg1 Int)(arg2 Int)(arg3 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (arg0 arg1 arg2 arg3 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= J5 (not (<= i!M0 100))) (= J8 (not (<= j!M0 k!M0)))) (= tmp!12 i!M0)) (= i!16 j!M0)) (= j!22 (+ 1 tmp!12))) (= k!28 (+ (- 1) k!M0))) (=> (and (not J5) (not J8)) (= tmpPostExec k!28))) (=> (and (not J5) (not J8)) (= kPostExec i!16))) (=> (and (not J5) (not J8)) (= iPostExec j!22))) (=> (and (not J5) (not J8)) (= jPostExec tmp!12))) (and (not J5) (not J8))) (= inB8 (not (<= inI6 100)))) (= inB3 (not (<= inI0 inI7)))) (= tmp!M0 inI6)) (= i!M0 inI0)) (= j!M0 (+ 1 tmp!M0))) (= k!M0 (+ (- 1) inI7))) (and (not inB8) (not inB3))) (and (> (rankingFunction!0 tmp!M0 k!M0 i!M0 j!M0 ) (rankingFunction!0 tmpPostExec kPostExec iPostExec jPostExec )) (>= (rankingFunction!0 tmp!M0 k!M0 i!M0 j!M0 ) 0))))
(check-synth)


