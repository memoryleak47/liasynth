(set-logic LIA)

(synth-fun qm-foo ((x Int)
     (y Int)
    )
   Int)

(declare-var x Int)

(declare-var y Int)

(constraint (= (qm-foo x y)
     (ite (<= x y)
       y x)
    )
  )

(check-synth)

