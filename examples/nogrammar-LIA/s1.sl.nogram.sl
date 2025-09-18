(set-logic LIA)

(synth-fun f ((x Int)
    )
   Int)

(declare-var x Int)

(constraint (= (f 0)
     0)
  )

(constraint (= (f 1)
     10)
  )

(constraint (= (f 2)
     20)
  )

(constraint (= (f 3)
     30)
  )

(constraint (= (f 4)
     40)
  )

(constraint (= (f 5)
     50)
  )

(constraint (or (and (> x 5)
       (= (f x)
         x)
      )
     (<= x 5)
    )
  )

(check-synth)

