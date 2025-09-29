; printing sygus problem  

(set-logic LIA)
(declare-var data.length_290-29-290-44 Int)

(synth-fun __SYNTHFUN_f_290-29-290-44((data.length Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (data.length 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (or (and (=> (= data.length_290-29-290-44 0) (= (__SYNTHFUN_f_290-29-290-44 data.length_290-29-290-44 ) false)) (and (=> (= data.length_290-29-290-44 0) (= (__SYNTHFUN_f_290-29-290-44 data.length_290-29-290-44 ) false)) (and (=> (= data.length_290-29-290-44 1) (= (__SYNTHFUN_f_290-29-290-44 data.length_290-29-290-44 ) true)) (=> (= data.length_290-29-290-44 3) (= (__SYNTHFUN_f_290-29-290-44 data.length_290-29-290-44 ) true))))) (and (=> (= data.length_290-29-290-44 0) (= (__SYNTHFUN_f_290-29-290-44 data.length_290-29-290-44 ) true)) (and (=> (= data.length_290-29-290-44 0) (= (__SYNTHFUN_f_290-29-290-44 data.length_290-29-290-44 ) false)) (and (=> (= data.length_290-29-290-44 1) (= (__SYNTHFUN_f_290-29-290-44 data.length_290-29-290-44 ) true)) (=> (= data.length_290-29-290-44 3) (= (__SYNTHFUN_f_290-29-290-44 data.length_290-29-290-44 ) true)))))))
(check-synth)


