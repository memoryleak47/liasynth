(set-logic LIA)

(synth-fun qm-foo ((x Int) (y Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x y 0 1 (- Start Start) (+ Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((< Start Start)))))

(declare-var x Int)
(declare-var y Int)
(constraint (= (qm-foo x y) (ite (<= x y) y x)))

(check-synth)

