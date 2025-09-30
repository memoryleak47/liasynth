; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(synth-fun f((x Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (= (f 0 ) 0))
(constraint (= (f 1 ) 10))
(constraint (= (f 2 ) 20))
(constraint (= (f 3 ) 30))
(constraint (= (f 4 ) 40))
(constraint (= (f 5 ) 50))
(constraint (= (f 6 ) 6))
(constraint (= (f 7 ) 7))
(constraint (= (f 8 ) 8))
(constraint (= (f 9 ) 9))
(constraint (= (f 10 ) 10))
(check-synth)


