(set-logic LIA)

(synth-fun max2 ((x Int) (y Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x y 0 1 (ite (> x y) Start Start) (+ (+ 10 Start) Start)))
    ))

(declare-var x Int)
(declare-var y Int)
(constraint (= (max2 x y) (+ (+ 10 x) y)))

(check-synth)
