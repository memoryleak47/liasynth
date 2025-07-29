(set-logic LIA)

(synth-fun stupidprog ((x Int) (y Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x y 0 1 (+ Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((< Start Start)))))

(declare-var x Int)
(declare-var y Int)
(constraint (= (stupidprog x y) (+ x y)))

(check-synth)
