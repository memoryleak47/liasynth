(set-logic LIA)

(synth-fun qm-choose ((x Int)
     (y Int)
     (z Int)
    )
   Int)

(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(constraint (= (qm-choose x y z)
     (ite (and (< y x)
         (< x z)
        )
       1 0)
    )
  )

(check-synth)

