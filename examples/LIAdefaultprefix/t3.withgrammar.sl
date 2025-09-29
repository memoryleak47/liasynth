; printing sygus problem  

(set-logic LIA)
(declare-var this.y_122-16-122-32 Int)

(declare-var this.x_122-16-122-32 Int)

(declare-var y_122-16-122-32 Int)

(declare-var x_122-16-122-32 Int)

(synth-fun __SYNTHFUN_f_122-16-122-32((this.y Int)(this.x Int)(y Int)(x Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (this.y this.x y x 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (=> (and (= y_122-16-122-32 2) (and (= x_122-16-122-32 1) (and (= this.y_122-16-122-32 2) (= this.x_122-16-122-32 1)))) (= (__SYNTHFUN_f_122-16-122-32 this.y_122-16-122-32 this.x_122-16-122-32 y_122-16-122-32 x_122-16-122-32 ) true)))
(constraint (=> (and (= y_122-16-122-32 3) (and (= x_122-16-122-32 1) (and (= this.y_122-16-122-32 2) (= this.x_122-16-122-32 1)))) (= (__SYNTHFUN_f_122-16-122-32 this.y_122-16-122-32 this.x_122-16-122-32 y_122-16-122-32 x_122-16-122-32 ) false)))
(check-synth)


