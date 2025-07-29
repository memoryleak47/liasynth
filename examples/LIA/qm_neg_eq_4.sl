(set-logic LIA)

(synth-fun qm-foo ((w Int) (x Int) (y Int) (z Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (w x y z 0 1 (- Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((< Start Start)))))

(declare-var w Int)
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(constraint (= (qm-foo w x y z) (ite (and (<= w 0) (and (<= x 0) (and (<= y 0) (<= z 0)))) 1 0)))

(check-synth)

