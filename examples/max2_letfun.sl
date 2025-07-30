(set-logic LIA)

(synth-fun max2 ((x Int) (y Int)) Int
((Start Int) (StartBool Bool))
((Start Int (x y 0 1 (+ Start Start) (- Start Start) (ite StartBool Start Start)))
(StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start)))))

(declare-var x Int)
(declare-var y Int)

(define-fun max-f ((a Int) (b Int)) Int (ite (> a b) a b))

(constraint (let ((m1 (max-f x y)) (m2 (max2 x y))) (= m1 m2)))

(check-synth)
