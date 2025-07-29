(set-logic LIA)

(synth-fun qm-choose ((x Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x 0 1 (- Start Start) (+ Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((< Start Start)))))

(declare-var x Int)
(constraint (= (qm-choose x) (ite (<= x 0) 1 0)))

(check-synth)

