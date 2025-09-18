(set-logic LIA)

(synth-fun qm-loop ((x Int)
    )
   Int)

(declare-var x Int)

(constraint (= (qm-loop x)
     (ite (<= x 0)
       3 (- x 1)
      )
    )
  )

(check-synth)

