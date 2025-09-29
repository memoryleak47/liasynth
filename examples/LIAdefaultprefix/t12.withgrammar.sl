; printing sygus problem  

(set-logic LIA)
(declare-var pair.length_29-21-29-36 Int)

(synth-fun __SYNTHFUN_f_29-21-29-36((pair.length Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (pair.length 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (or (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true))))) (and (=> (= pair.length_29-21-29-36 1) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) false)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 1) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) false)) (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)))))))))
(check-synth)


