(set-logic LIA)

(synth-fun qm-choose ((x Int)
    )
   Int)

(declare-var x Int)

(constraint (= (qm-choose x)
     (ite (<= x 0)
       1 0)
    )
  )

(check-synth)

