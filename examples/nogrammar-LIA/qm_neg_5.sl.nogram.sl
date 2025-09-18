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
     (ite (and (< v 0)
         (and (< w 0)
           (and (< x 0)
             (and (< y 0)
               (< z 0)
              )
            )
          )
        )
       1 0)
    )
  )

(check-synth)

