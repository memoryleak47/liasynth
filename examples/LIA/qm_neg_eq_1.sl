(set-logic LIA)

(synth-fun qm-foo ((x Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x 0 1 (- Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((< Start Start)))))

(declare-var x Int)
(constraint (= (qm-foo x) (ite (<= x 0) 1 0)))

(check-synth)

