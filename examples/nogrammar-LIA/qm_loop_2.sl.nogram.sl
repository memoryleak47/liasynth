(set-logic LIA)

(synth-fun qm-multi-loop ((x Int)
     (y Int)
    )
   Int)

(declare-var x Int)

(declare-var y Int)

(constraint (or (or (< x 0)
       (< y 0)
      )
     (= (qm-multi-loop x y)
       (ite (= y 0)
         (ite (= x 0)
           3 (- x 1)
          )
         x)
      )
    )
  )

(check-synth)

