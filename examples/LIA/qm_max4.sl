(set-logic LIA)

(synth-fun qm-foo ((w Int) (x Int) (y Int) (z Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (w x y z 0 1 (- Start Start) (+ Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((< Start Start)))))

(declare-var w Int)
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(constraint (= (qm-foo w x y z) (ite (and (and (>= w x) (>= w y)) (>= w z)) w (ite (and (>= x y) (>= x z)) x (ite (>= y z) y z)))))

(check-synth)

