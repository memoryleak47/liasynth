; printing sygus problem  

(set-logic LIA)
(declare-var x1 Int)

(declare-var x2 Int)

(declare-var x3 Int)

(declare-var x4 Int)

(declare-var k Int)

(synth-fun __SYNTHFUN_findIdx((y1 Int)(y2 Int)(y3 Int)(y4 Int)(k1 Int)) Int
((Start Int)(BoolExpr Bool))
((Start Int (0 1 2 3 4 y1 y2 y3 y4 k1 (ite BoolExpr Start Start) ))
(BoolExpr Bool ((< Start Start) (<= Start Start) (> Start Start) (>= Start Start) ))
)
)

(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (< k x1) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 k ) 0))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (> k x4) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 k ) 4))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (and (> k x1) (< k x2)) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 k ) 1))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (and (> k x2) (< k x3)) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 k ) 2))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (< x3 x4))) (=> (and (> k x3) (< k x4)) (= (__SYNTHFUN_findIdx x1 x2 x3 x4 k ) 3))))
(check-synth)


