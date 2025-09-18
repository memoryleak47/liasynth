(set-logic LIA)

(synth-fun constant ((x Int)
    )
   Int)

(declare-var x Int)

(declare-var y Int)

(constraint (= (constant x)
     (constant y)
    )
  )

(check-synth)

