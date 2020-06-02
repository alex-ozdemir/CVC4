; COMMAND-LINE: --no-check-unsat-cores
; COMMAND-LINE: --proof-new --no-proof --no-check-unsat-cores --no-check-proofs
; EXPECT: unsat
(set-logic QF_LIA)

(declare-fun i () Int)
(declare-fun j () Int)

(assert (> (+ i j) 1))
(assert (< i 1))
(assert (< j 1))

(check-sat)
