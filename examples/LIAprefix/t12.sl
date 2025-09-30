; printing sygus problem  

(set-logic LIA)
(declare-var pair.length_29-21-29-36 Int)

(synth-fun __SYNTHFUN_f_29-21-29-36((pair.length Int)) Bool
((Start Bool)(IntExpr Int))
((Start Bool ((> IntExpr IntExpr) (>= IntExpr IntExpr) ))
(IntExpr Int (pair.length 0 1 ))
)
)

(constraint (or (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true))))) (and (=> (= pair.length_29-21-29-36 1) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) false)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)) (and (=> (= pair.length_29-21-29-36 1) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) false)) (=> (= pair.length_29-21-29-36 2) (= (__SYNTHFUN_f_29-21-29-36 pair.length_29-21-29-36 ) true)))))))))
(check-synth)


