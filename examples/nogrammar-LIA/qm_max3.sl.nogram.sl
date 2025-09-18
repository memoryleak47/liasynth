(set-logic LIA)

(synth-fun qm-foo ((x Int)
     (y Int)
     (z Int)
    )
   Int)

(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(constraint (= (qm-foo x y z)
     (ite (and (>= x y)
         (>= x z)
        )
       x (ite (>= y z)
         y z)
      )
    )
  )

(check-synth)

