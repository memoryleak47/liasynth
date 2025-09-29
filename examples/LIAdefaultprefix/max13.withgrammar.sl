; printing sygus problem  

(set-logic LIA)
(declare-var x1 Int)

(declare-var x2 Int)

(declare-var x3 Int)

(declare-var x4 Int)

(declare-var x5 Int)

(declare-var x6 Int)

(declare-var x7 Int)

(declare-var x8 Int)

(declare-var x9 Int)

(declare-var x10 Int)

(declare-var x11 Int)

(declare-var x12 Int)

(declare-var x13 Int)

(synth-fun __SYNTHFUN_max13((x1 Int)(x2 Int)(x3 Int)(x4 Int)(x5 Int)(x6 Int)(x7 Int)(x8 Int)(x9 Int)(x10 Int)(x11 Int)(x12 Int)(x13 Int)) Int
((NTInt Int)(NTbool Bool))
((NTInt Int (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
(NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
)
)

(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x1))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x2))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x3))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x4))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x5))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x6))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x7))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x8))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x9))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x10))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x11))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x12))
(constraint (>= (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ) x13))
(constraint (or (= x1 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x2 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x3 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x4 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x5 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x6 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x7 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x8 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x9 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x10 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x11 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (or (= x12 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )) (= x13 (__SYNTHFUN_max13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 )))))))))))))))
(check-synth)


