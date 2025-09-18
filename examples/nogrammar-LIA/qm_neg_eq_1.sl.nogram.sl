(set-logic LIA)

(synth-fun qm-foo ((x Int)
    )
   Int)

(declare-var x Int)

(constraint (= (qm-foo x)
     (ite (<= x 0)
       1 0)
    )
  )

(check-synth)

