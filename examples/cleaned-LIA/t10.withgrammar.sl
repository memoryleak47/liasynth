; printing sygus problem  

(set-logic LIA)
(declare-var this.total_35-7-35-46 Int)

(declare-var this.num_35-7-35-46 Int)

(declare-var this.start_35-7-35-46 Int)

(synth-fun f_35-7-35-46((this.total Int)(this.num Int)(this.start Int)) Bool
((NTbool Bool)(NTInt Int))
((NTbool Bool ((not NTbool) (and NTbool NTbool) (or NTbool NTbool) (ite NTbool NTbool NTbool) (= NTInt NTInt) (< NTInt NTInt) (> NTInt NTInt) ))
(NTInt Int (this.total this.num this.start 0 1 (- NTInt) (+ NTInt NTInt) (- NTInt NTInt) (ite NTbool NTInt NTInt) ))
)
)

(constraint (=> (and (= this.num_35-7-35-46 1) (and (= this.start_35-7-35-46 0) (= this.total_35-7-35-46 2))) (= (f_35-7-35-46 this.total_35-7-35-46 this.num_35-7-35-46 this.start_35-7-35-46 ) false)))
(check-synth)


