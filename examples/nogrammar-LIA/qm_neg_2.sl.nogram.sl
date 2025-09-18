(set-logic LIA)

(synth-fun qm-foo ((x Int)
     (y Int)
    )
   Int)

(declare-var x Int)

(declare-var y Int)

(constraint (= (qm-foo x y)
     (ite (and (< x 0)
         (< y 0)
        )
       1 0)
    )
  )

(check-synth)

