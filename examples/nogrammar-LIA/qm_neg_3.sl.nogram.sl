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
     (ite (and (< x 0)
         (and (< y 0)
           (< z 0)
          )
        )
       1 0)
    )
  )

(check-synth)

