(set-logic LIA)

(synth-fun f ((x Int)
     (y Int)
    )
   Int)

(declare-var x Int)

(declare-var y Int)

(constraint (or (and (= x y)
       (= (f x y)
         (+ x y)
        )
      )
     (or (and (> x y)
         (= (f x y)
           1)
        )
       (= (f x y)
         (- 1)
        )
      )
    )
  )

(check-synth)

