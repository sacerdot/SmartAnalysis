; z3 -in  per la versione interattiva
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (> a (+ b 2)))
(assert (< a (+ (* 3 b) 3)))
(check-sat)
(get-model)

