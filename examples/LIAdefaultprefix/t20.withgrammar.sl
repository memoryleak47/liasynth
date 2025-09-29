; printing sygus problem  

(set-logic LIA)
(declare-var next_68-13-68-36 Int)

(declare-var pos_68-13-68-36 Int)

(declare-var MC_741360_68-13-68-36 Bool)

(synth-fun __SYNTHFUN_f_68-13-68-36((next Int)(pos Int)(MC_741360 Bool)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool (MC_741360 (not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (next pos 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (and (=> (and (= pos_68-13-68-36 9) (and (= next_68-13-68-36 46) (= MC_741360_68-13-68-36 false))) (= (__SYNTHFUN_f_68-13-68-36 next_68-13-68-36 pos_68-13-68-36 MC_741360_68-13-68-36 ) true)) (and (=> (and (= pos_68-13-68-36 8) (and (= next_68-13-68-36 55) (= MC_741360_68-13-68-36 true))) (= (__SYNTHFUN_f_68-13-68-36 next_68-13-68-36 pos_68-13-68-36 MC_741360_68-13-68-36 ) true)) (=> (and (= MC_741360_68-13-68-36 true) (and (= next_68-13-68-36 56) (= pos_68-13-68-36 10))) (= (__SYNTHFUN_f_68-13-68-36 next_68-13-68-36 pos_68-13-68-36 MC_741360_68-13-68-36 ) true)))))
(constraint (and (=> (and (= pos_68-13-68-36 9) (and (= next_68-13-68-36 46) (= MC_741360_68-13-68-36 false))) (= (__SYNTHFUN_f_68-13-68-36 next_68-13-68-36 pos_68-13-68-36 MC_741360_68-13-68-36 ) true)) (and (=> (and (= pos_68-13-68-36 8) (and (= next_68-13-68-36 55) (= MC_741360_68-13-68-36 true))) (= (__SYNTHFUN_f_68-13-68-36 next_68-13-68-36 pos_68-13-68-36 MC_741360_68-13-68-36 ) true)) (=> (and (= MC_741360_68-13-68-36 true) (and (= next_68-13-68-36 56) (= pos_68-13-68-36 10))) (= (__SYNTHFUN_f_68-13-68-36 next_68-13-68-36 pos_68-13-68-36 MC_741360_68-13-68-36 ) true)))))
(check-synth)


