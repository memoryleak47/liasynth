(set-logic LIA)

(define-fun max-f ((a Int) (b Int)) Int (ite (> a b) a b))

(synth-fun max2 ((x Int) (y Int)) Int
((Start Int))
    ((Start Int (x y 0 1 (+ (max-f Start x) Start) (+ x x) (- Start Start) (max-f Start Start)))))


(declare-var x Int)
(declare-var y Int)
(constraint (>= (max2 x y) x))
(constraint (>= (max2 x y) y))
(constraint (or (= x (max2 x y)) (= y (max2 x y))))

(check-synth)
