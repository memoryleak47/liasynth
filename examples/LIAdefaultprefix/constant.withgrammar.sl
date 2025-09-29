; printing sygus problem  

(set-logic LIA)
(declare-var x Int)

(declare-var y Int)

(synth-fun __SYNTHFUN_constant((x Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (= (__SYNTHFUN_constant x ) (__SYNTHFUN_constant y )))
(check-synth)


