; SMTLIB-v2 
; result is unsat 
(set-logic LIA)
(define-fun f_119-13-119-51 ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int) 
    (x7 Int) (x8 Int) (x9 Int) (x10 Int) (x11 Int) (x12 Int)) Bool
(ite (and (= x3 1)(= x8 0) (= x7 11)(= x5 3)(= x12 1) (= x11 0)(= x1 0) (= x2 0) (= x6 0)(= x4 10)
(= x10 2)
(= x9 10))
false
(ite (= x12 1) true false)))



(declare-fun stopTime_119-13-119-51  () Int)
(declare-fun this.stopTime_119-13-119-51  () Int)
(declare-fun org.apache.commons.lang.time.StopWatch.STATE_RUNNING_119-13-119-51  () Int)
(declare-fun this.splitState_119-13-119-51  () Int)
(declare-fun org.apache.commons.lang.time.StopWatch.STATE_SUSPENDED_119-13-119-51  () Int)
(declare-fun org.apache.commons.lang.time.StopWatch.STATE_UNSTARTED_119-13-119-51  () Int)
(declare-fun this.startTime_119-13-119-51  () Int)
(declare-fun org.apache.commons.lang.time.StopWatch.STATE_SPLIT_119-13-119-51  () Int)
(declare-fun org.apache.commons.lang.time.StopWatch.STATE_UNSPLIT_119-13-119-51  () Int)
(declare-fun org.apache.commons.lang.time.StopWatch.STATE_STOPPED_119-13-119-51  () Int)
(declare-fun MC_741360_119-13-119-51  () Int)
(declare-fun this.runningState_119-13-119-51  () Int)
(assert (or (not (=> (and (= org.apache.commons.lang.time.StopWatch.STATE_RUNNING_119-13-119-51 1) (and (= org.apache.commons.lang.time.StopWatch.STATE_SPLIT_119-13-119-51 11) (and (= this.startTime_119-13-119-51 0) (and (= org.apache.commons.lang.time.StopWatch.STATE_SUSPENDED_119-13-119-51 3) (and (= this.runningState_119-13-119-51 3) (and (= MC_741360_119-13-119-51 0) (and (= stopTime_119-13-119-51 0) (and (= this.stopTime_119-13-119-51 0) (and (= org.apache.commons.lang.time.StopWatch.STATE_UNSTARTED_119-13-119-51 0) (and (= this.splitState_119-13-119-51 10) (and (= org.apache.commons.lang.time.StopWatch.STATE_STOPPED_119-13-119-51 2) (= org.apache.commons.lang.time.StopWatch.STATE_UNSPLIT_119-13-119-51 10)))))))))))) (= (f_119-13-119-51 stopTime_119-13-119-51 this.stopTime_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_RUNNING_119-13-119-51 this.splitState_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_SUSPENDED_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_UNSTARTED_119-13-119-51 this.startTime_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_SPLIT_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_UNSPLIT_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_STOPPED_119-13-119-51 MC_741360_119-13-119-51 this.runningState_119-13-119-51) false)))(not (or (=> (and (= org.apache.commons.lang.time.StopWatch.STATE_RUNNING_119-13-119-51 1) (and (= org.apache.commons.lang.time.StopWatch.STATE_SPLIT_119-13-119-51 11) (and (= this.startTime_119-13-119-51 0) (and (= org.apache.commons.lang.time.StopWatch.STATE_SUSPENDED_119-13-119-51 3) (and (= this.runningState_119-13-119-51 1) (and (= MC_741360_119-13-119-51 0) (and (= stopTime_119-13-119-51 0) (and (= this.stopTime_119-13-119-51 0) (and (= org.apache.commons.lang.time.StopWatch.STATE_UNSTARTED_119-13-119-51 0) (and (= this.splitState_119-13-119-51 10) (and (= org.apache.commons.lang.time.StopWatch.STATE_STOPPED_119-13-119-51 2) (= org.apache.commons.lang.time.StopWatch.STATE_UNSPLIT_119-13-119-51 10)))))))))))) (= (f_119-13-119-51 stopTime_119-13-119-51 this.stopTime_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_RUNNING_119-13-119-51 this.splitState_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_SUSPENDED_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_UNSTARTED_119-13-119-51 this.startTime_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_SPLIT_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_UNSPLIT_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_STOPPED_119-13-119-51 MC_741360_119-13-119-51 this.runningState_119-13-119-51) false)) (=> (and (= org.apache.commons.lang.time.StopWatch.STATE_RUNNING_119-13-119-51 1) (and (= org.apache.commons.lang.time.StopWatch.STATE_SPLIT_119-13-119-51 11) (and (= this.startTime_119-13-119-51 0) (and (= org.apache.commons.lang.time.StopWatch.STATE_SUSPENDED_119-13-119-51 3) (and (= this.runningState_119-13-119-51 1) (and (= MC_741360_119-13-119-51 0) (and (= stopTime_119-13-119-51 0) (and (= this.stopTime_119-13-119-51 0) (and (= org.apache.commons.lang.time.StopWatch.STATE_UNSTARTED_119-13-119-51 0) (and (= this.splitState_119-13-119-51 10) (and (= org.apache.commons.lang.time.StopWatch.STATE_STOPPED_119-13-119-51 2) (= org.apache.commons.lang.time.StopWatch.STATE_UNSPLIT_119-13-119-51 10)))))))))))) (= (f_119-13-119-51 stopTime_119-13-119-51 this.stopTime_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_RUNNING_119-13-119-51 this.splitState_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_SUSPENDED_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_UNSTARTED_119-13-119-51 this.startTime_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_SPLIT_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_UNSPLIT_119-13-119-51 org.apache.commons.lang.time.StopWatch.STATE_STOPPED_119-13-119-51 MC_741360_119-13-119-51 this.runningState_119-13-119-51) true))))))
(check-sat)
(get-model)

