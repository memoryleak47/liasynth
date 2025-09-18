(set-logic LIA)

(synth-fun qm-foo ((v Int)
     (w Int)
     (x Int)
     (y Int)
     (z Int)
    )
   Int)

(declare-var v Int)

(declare-var w Int)

(declare-var x Int)

(declare-var y Int)

(declare-var z Int)

(constraint (= (qm-foo v w x y z)
     (ite (and (and (and (>= v w)
             (>= v x)
            )
           (>= v y)
          )
         (>= v z)
        )
       v (ite (and (and (>= w x)
             (>= w y)
            )
           (>= w z)
          )
         w (ite (and (>= x y)
             (>= x z)
            )
           x (ite (>= y z)
             y z)
          )
        )
      )
    )
  )

(check-synth)

