; printing sygus problem  

(set-logic LIA)
(declare-var NOACK_97-10-97-48 Int)

(declare-var this.acknowledgeId_97-10-97-48 Int)

(declare-var enabled_97-10-97-48 Bool)

(synth-fun __SYNTHFUN_f_97-10-97-48((NOACK Int)(this.acknowledgeId Int)(enabled Bool)) Bool
((Start Bool)(IntExpr Int))
((Start Bool ((and Start Start) (= IntExpr IntExpr) (not Start) (or Start Start) enabled ))
(IntExpr Int (NOACK this.acknowledgeId 0 1 ))
)
)

(constraint (=> (and (= NOACK_97-10-97-48 48) (and (= enabled_97-10-97-48 true) (= this.acknowledgeId_97-10-97-48 48))) (= (__SYNTHFUN_f_97-10-97-48 NOACK_97-10-97-48 this.acknowledgeId_97-10-97-48 enabled_97-10-97-48 ) true)))
(check-synth)


