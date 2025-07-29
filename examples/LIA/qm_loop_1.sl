(set-logic LIA)

(synth-fun qm-loop ((x Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x 0 1 3 (+ Start Start) (- Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((< Start Start)))))

(declare-var x Int)
(constraint (= (qm-loop x) (ite (<= x 0) 3 (- x 1))))

(check-synth)

