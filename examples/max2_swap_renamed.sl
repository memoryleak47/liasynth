(set-logic LIA)

(synth-fun max2 ((x Int) (y Int)) Int
((Start Int) (StartBool Bool))
((Start Int (x y 0 1 (+ Start Start) (- Start Start) (ite StartBool Start Start)))
(StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start)))))

(declare-var x_r Int)
(declare-var y_r Int)

(constraint (= (max2 x_r y_r) (max2 y_r x_r)))
(constraint (>= (max2 x_r y_r) x_r))
(constraint (>= (max2 x_r y_r) y_r))
(constraint (or (= x_r (max2 x_r y_r)) (= y_r (max2 x_r y_r))))

(check-synth)
