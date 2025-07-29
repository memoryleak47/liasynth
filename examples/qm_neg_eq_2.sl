(set-logic LIA)

(synth-fun qm-foo ((x Int) (y Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x y 0 1 (- Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((< Start Start)))))

(declare-var x Int)
(declare-var y Int)
(constraint (= (qm-foo x y) (ite (and (<= x 0) (<= y 0)) 1 0)))

(check-synth)
